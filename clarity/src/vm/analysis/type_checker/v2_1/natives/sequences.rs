// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020 Stacks Open Internet Foundation
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use std::iter;

use clarity_types::errors::analysis::{get_arguments_at_least, get_arguments_exact};
use stacks_common::types::StacksEpochId;

use super::{SimpleNativeFunction, TypedNativeFunction};
use crate::vm::analysis::type_checker::v2_1::{
    CheckError, CheckErrors, TypeChecker, TypingContext,
};
use crate::vm::costs::cost_functions::ClarityCostFunction;
use crate::vm::costs::{analysis_typecheck_cost, runtime_cost, CostTracker};
use crate::vm::diagnostic::Diagnostic;
use crate::vm::functions::NativeFunctions;
use crate::vm::representations::{SymbolicExpression, SymbolicExpressionType};
pub use crate::vm::types::signatures::{BufferLength, ListTypeData, StringUTF8Length, BUFF_1};
use crate::vm::types::SequenceSubtype::*;
use crate::vm::types::StringSubtype::*;
use crate::vm::types::{FunctionType, TypeSignature, Value};

fn get_simple_native_or_user_define(
    function_name: &str,
    checker: &mut TypeChecker,
) -> Result<FunctionType, CheckError> {
    runtime_cost(ClarityCostFunction::AnalysisLookupFunction, checker, 0)?;
    if let Some(ref native_function) =
        NativeFunctions::lookup_by_name_at_version(function_name, &checker.clarity_version)
    {
        if let TypedNativeFunction::Simple(SimpleNativeFunction(function_type)) =
            TypedNativeFunction::type_native_function(native_function)?
        {
            Ok(function_type)
        } else {
            Err(CheckErrors::IllegalOrUnknownFunctionApplication(function_name.to_string()).into())
        }
    } else {
        checker.get_function_type(function_name).ok_or(
            CheckErrors::IllegalOrUnknownFunctionApplication(function_name.to_string()).into(),
        )
    }
}

pub fn check_special_map(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let ([fname_arg, first_arg], rest_arg) = get_arguments_at_least(args)?;

    let function_name = fname_arg
        .match_atom()
        .ok_or(CheckErrors::NonFunctionApplication)?;
    // we will only lookup native or defined functions here.
    //   you _cannot_ map a special function.
    let function_type = get_simple_native_or_user_define(function_name, checker)?;
    runtime_cost(
        ClarityCostFunction::AnalysisIterableFunc,
        checker,
        args.len(),
    )?;

    // chain together the first map argument and any additionally supplied arguments
    //  for variadic maps
    let iter = iter::once(first_arg).chain(rest_arg.iter());
    let mut min_args = u32::MAX;

    // use func_type visitor pattern
    let mut accumulated_type = None;
    let mut total_costs = vec![];
    let mut check_result = Ok(());
    let mut accumulated_types = Vec::new();

    for (arg_ix, arg) in iter.enumerate() {
        let argument_type = checker.type_check(arg, context)?;
        let entry_type = match argument_type {
            TypeSignature::SequenceType(sequence) => {
                let (entry_type, len) = match sequence {
                    ListType(list_data) => list_data.destruct(),
                    BufferType(buffer_data) => (TypeSignature::min_buffer()?, buffer_data.into()),
                    StringType(ASCII(ascii_data)) => {
                        (TypeSignature::min_string_ascii()?, ascii_data.into())
                    }
                    StringType(UTF8(utf8_data)) => {
                        (TypeSignature::min_string_utf8()?, utf8_data.into())
                    }
                };
                min_args = min_args.min(len);
                entry_type
            }
            _ => {
                // Note: we could, if we want, enable this:
                // (map + (list 1 1 1) 1) -> (list 2 2 2)
                // However that could lead to confusions when combining certain types:
                // ex: (map concat (list "hello " "hi ") "world") would fail, because
                // strings are handled as sequences.
                return Err(CheckErrors::ExpectedSequence(Box::new(argument_type)).into());
            }
        };

        if check_result.is_ok() {
            let (costs, result) = function_type.check_args_visitor_2_1(
                checker,
                &entry_type,
                arg_ix,
                accumulated_type.as_ref(),
            );
            // add the accumulated type and total cost *before*
            //  checking for an error: we want the subsequent error handling
            //  to account for this cost
            accumulated_types.push(entry_type);
            total_costs.extend(costs);

            match result {
                Ok(Some(returned_type)) => {
                    accumulated_type = Some(returned_type);
                }
                Ok(None) => {}
                Err(e) => {
                    check_result = Err(e);
                }
            };
        }
    }

    if let Err(mut check_error) = check_result {
        if let CheckErrors::IncorrectArgumentCount(expected, _actual) = *check_error.err {
            check_error.err = Box::new(CheckErrors::IncorrectArgumentCount(
                expected,
                args.len().saturating_sub(1),
            ));
            check_error.diagnostic = Diagnostic::err(check_error.err.as_ref());
        }
        // accumulate the checking costs
        for cost in total_costs.into_iter() {
            checker.add_cost(cost?)?;
        }

        return Err(check_error);
    }

    let mapped_type = function_type.check_args(
        checker,
        &accumulated_types,
        context.epoch,
        context.clarity_version,
    )?;
    TypeSignature::list_of(mapped_type, min_args)
        .map_err(|_| CheckErrors::ConstructedListTooLarge.into())
}

pub fn check_special_filter(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let [fname_arg, iterable_arg] = get_arguments_exact(args)?;

    let function_name = fname_arg
        .match_atom()
        .ok_or(CheckErrors::NonFunctionApplication)?;
    // we will only lookup native or defined functions here.
    //   you _cannot_ map a special function.
    let function_type = get_simple_native_or_user_define(function_name, checker)?;

    runtime_cost(ClarityCostFunction::AnalysisIterableFunc, checker, 0)?;
    let argument_type = checker.type_check(iterable_arg, context)?;

    {
        let input_type = match argument_type {
            TypeSignature::SequenceType(ref sequence_type) => Ok(sequence_type.unit_type()?),
            _ => Err(CheckErrors::ExpectedSequence(Box::new(
                argument_type.clone(),
            ))),
        }?;

        let filter_type = function_type.check_args(
            checker,
            &[input_type],
            context.epoch,
            context.clarity_version,
        )?;

        if TypeSignature::BoolType != filter_type {
            return Err(CheckErrors::TypeError(
                Box::new(TypeSignature::BoolType),
                Box::new(filter_type),
            )
            .into());
        }
    }

    Ok(argument_type)
}

pub fn check_special_fold(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let [fname_arg, iterable_arg, init_arg] = get_arguments_exact(args)?;

    let function_name = fname_arg
        .match_atom()
        .ok_or(CheckErrors::NonFunctionApplication)?;
    // we will only lookup native or defined functions here.
    //   you _cannot_ fold a special function.
    let function_type = get_simple_native_or_user_define(function_name, checker)?;

    runtime_cost(ClarityCostFunction::AnalysisIterableFunc, checker, 0)?;
    let argument_type = checker.type_check(iterable_arg, context)?;

    let input_type = match argument_type {
        TypeSignature::SequenceType(sequence_type) => Ok(sequence_type.unit_type()?),
        _ => Err(CheckErrors::ExpectedSequence(Box::new(argument_type))),
    }?;

    let initial_value_type = checker.type_check(init_arg, context)?;

    // fold: f(A, B) -> A
    //     where A = initial_value_type
    //           B = list items type

    // f must accept the initial value and the list items type
    let return_type = function_type.check_args(
        checker,
        &[input_type.clone(), initial_value_type],
        context.epoch,
        context.clarity_version,
    )?;

    // f must _also_ accepts its own return type!
    let return_type = function_type.check_args(
        checker,
        &[input_type, return_type],
        context.epoch,
        context.clarity_version,
    )?;

    Ok(return_type)
}

pub fn check_special_concat(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let [lhs, rhs] = get_arguments_exact(args)?;

    let lhs_type = checker.type_check(lhs, context)?;
    let rhs_type = checker.type_check(rhs, context)?;

    runtime_cost(ClarityCostFunction::AnalysisIterableFunc, checker, 0)?;

    analysis_typecheck_cost(checker, &lhs_type, &rhs_type)?;

    let res = match (&lhs_type, &rhs_type) {
        (TypeSignature::SequenceType(lhs_seq), TypeSignature::SequenceType(rhs_seq)) => {
            match (lhs_seq, rhs_seq) {
                (ListType(lhs_list), ListType(rhs_list)) => {
                    let (lhs_entry_type, lhs_max_len) =
                        (lhs_list.get_list_item_type(), lhs_list.get_max_len());
                    let (rhs_entry_type, rhs_max_len) =
                        (rhs_list.get_list_item_type(), rhs_list.get_max_len());

                    let list_entry_type = TypeSignature::least_supertype(
                        &StacksEpochId::Epoch21,
                        lhs_entry_type,
                        rhs_entry_type,
                    )?;
                    let new_len = lhs_max_len
                        .checked_add(rhs_max_len)
                        .ok_or(CheckErrors::MaxLengthOverflow)?;
                    TypeSignature::list_of(list_entry_type, new_len)?
                }
                (BufferType(lhs_len), BufferType(rhs_len)) => {
                    let size: u32 = u32::from(lhs_len)
                        .checked_add(u32::from(rhs_len))
                        .ok_or(CheckErrors::MaxLengthOverflow)?;
                    TypeSignature::SequenceType(BufferType(size.try_into()?))
                }
                (StringType(ASCII(lhs_len)), StringType(ASCII(rhs_len))) => {
                    let size: u32 = u32::from(lhs_len)
                        .checked_add(u32::from(rhs_len))
                        .ok_or(CheckErrors::MaxLengthOverflow)?;
                    TypeSignature::SequenceType(StringType(ASCII(size.try_into()?)))
                }
                (StringType(UTF8(lhs_len)), StringType(UTF8(rhs_len))) => {
                    let size: u32 = u32::from(lhs_len)
                        .checked_add(u32::from(rhs_len))
                        .ok_or(CheckErrors::MaxLengthOverflow)?;
                    TypeSignature::SequenceType(StringType(UTF8(size.try_into()?)))
                }
                (_, _) => {
                    return Err(CheckErrors::TypeError(
                        Box::new(lhs_type.clone()),
                        Box::new(rhs_type.clone()),
                    )
                    .into())
                }
            }
        }
        _ => return Err(CheckErrors::ExpectedSequence(Box::new(lhs_type.clone())).into()),
    };
    Ok(res)
}

pub fn check_special_append(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let [lhs, rhs] = get_arguments_exact(args)?;

    runtime_cost(ClarityCostFunction::AnalysisIterableFunc, checker, 0)?;

    let lhs_type = checker.type_check(lhs, context)?;
    match lhs_type {
        TypeSignature::SequenceType(ListType(lhs_list)) => {
            let rhs_type = checker.type_check(rhs, context)?;
            let (lhs_entry_type, lhs_max_len) = lhs_list.destruct();

            analysis_typecheck_cost(checker, &lhs_entry_type, &rhs_type)?;

            let list_entry_type = TypeSignature::least_supertype(
                &StacksEpochId::Epoch21,
                &lhs_entry_type,
                &rhs_type,
            )?;
            let new_len = lhs_max_len
                .checked_add(1)
                .ok_or(CheckErrors::MaxLengthOverflow)?;
            let return_type = TypeSignature::list_of(list_entry_type, new_len)?;
            Ok(return_type)
        }
        _ => Err(CheckErrors::ExpectedListApplication.into()),
    }
}

pub fn check_special_as_max_len(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let [input, len_arg] = get_arguments_exact(args)?;

    let expected_len = match len_arg.expr {
        SymbolicExpressionType::LiteralValue(Value::UInt(expected_len)) => expected_len,
        _ => {
            let expected_len_type = checker.type_check(len_arg, context)?;
            return Err(CheckErrors::TypeError(
                Box::new(TypeSignature::UIntType),
                Box::new(expected_len_type),
            )
            .into());
        }
    };
    runtime_cost(
        ClarityCostFunction::AnalysisTypeAnnotate,
        checker,
        TypeSignature::UIntType.type_size()?,
    )?;
    checker
        .type_map
        .set_type(len_arg, TypeSignature::UIntType)?;

    let expected_len = u32::try_from(expected_len).map_err(|_e| CheckErrors::MaxLengthOverflow)?;

    let sequence = checker.type_check(input, context)?;
    runtime_cost(ClarityCostFunction::AnalysisIterableFunc, checker, 0)?;

    match sequence {
        TypeSignature::SequenceType(ListType(list)) => {
            let (lhs_entry_type, _) = list.destruct();
            let resized_list = ListTypeData::new_list(lhs_entry_type, expected_len)?;
            Ok(TypeSignature::OptionalType(Box::new(
                TypeSignature::SequenceType(ListType(resized_list)),
            )))
        }
        TypeSignature::SequenceType(BufferType(_)) => Ok(TypeSignature::OptionalType(Box::new(
            TypeSignature::SequenceType(BufferType(BufferLength::try_from(expected_len)?)),
        ))),
        TypeSignature::SequenceType(StringType(ASCII(_))) => Ok(TypeSignature::OptionalType(
            Box::new(TypeSignature::SequenceType(StringType(ASCII(
                BufferLength::try_from(expected_len)?,
            )))),
        )),
        TypeSignature::SequenceType(StringType(UTF8(_))) => Ok(TypeSignature::OptionalType(
            Box::new(TypeSignature::SequenceType(StringType(UTF8(
                StringUTF8Length::try_from(expected_len)?,
            )))),
        )),
        _ => Err(CheckErrors::ExpectedSequence(Box::new(sequence)).into()),
    }
}

pub fn check_special_len(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let [input] = get_arguments_exact(args)?;

    let collection_type = checker.type_check(input, context)?;
    runtime_cost(ClarityCostFunction::AnalysisIterableFunc, checker, 0)?;

    match collection_type {
        TypeSignature::SequenceType(_) => Ok(()),
        _ => Err(CheckErrors::ExpectedSequence(Box::new(collection_type))),
    }?;

    Ok(TypeSignature::UIntType)
}

pub fn check_special_element_at(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let [input, index] = get_arguments_exact(args)?;

    let _index_type = checker.type_check_expects(index, context, &TypeSignature::UIntType)?;

    let collection_type = checker.type_check(input, context)?;
    runtime_cost(ClarityCostFunction::AnalysisIterableFunc, checker, 0)?;

    match collection_type {
        TypeSignature::SequenceType(ListType(list)) => {
            let (entry_type, _) = list.destruct();
            TypeSignature::new_option(entry_type).map_err(|e| e.into())
        }
        TypeSignature::SequenceType(BufferType(_)) => {
            Ok(TypeSignature::OptionalType(Box::new(BUFF_1.clone())))
        }
        TypeSignature::SequenceType(StringType(ASCII(_))) => Ok(TypeSignature::OptionalType(
            Box::new(TypeSignature::SequenceType(StringType(ASCII(
                BufferLength::try_from(1u32)
                    .map_err(|_| CheckErrors::Expects("Bad constructor".into()))?,
            )))),
        )),
        TypeSignature::SequenceType(StringType(UTF8(_))) => Ok(TypeSignature::OptionalType(
            Box::new(TypeSignature::SequenceType(StringType(UTF8(
                StringUTF8Length::try_from(1u32)
                    .map_err(|_| CheckErrors::Expects("Bad constructor".into()))?,
            )))),
        )),
        _ => Err(CheckErrors::ExpectedSequence(Box::new(collection_type)).into()),
    }
}

pub fn check_special_index_of(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let [input, to_find] = get_arguments_exact(args)?;

    runtime_cost(ClarityCostFunction::AnalysisIterableFunc, checker, 0)?;
    let list_type = checker.type_check(input, context)?;

    let expected_input_type = match list_type {
        TypeSignature::SequenceType(ref sequence_type) => Ok(sequence_type.unit_type()?),
        _ => Err(CheckErrors::ExpectedSequence(Box::new(list_type))),
    }?;

    checker.type_check_expects(to_find, context, &expected_input_type)?;

    TypeSignature::new_option(TypeSignature::UIntType).map_err(|e| e.into())
}

/// This function type checks the Clarity2 function `slice?`.
pub fn check_special_slice(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let [input, left, right] = get_arguments_exact(args)?;

    runtime_cost(ClarityCostFunction::AnalysisIterableFunc, checker, 0)?;
    // Check sequence
    let seq_type = checker.type_check(input, context)?;
    let seq = match seq_type {
        TypeSignature::SequenceType(seq) => {
            TypeSignature::new_option(TypeSignature::SequenceType(seq))?
        }
        _ => return Err(CheckErrors::ExpectedSequence(Box::new(seq_type)).into()),
    };

    // Check left position argument
    checker.type_check_expects(left, context, &TypeSignature::UIntType)?;
    // Check right position argument
    checker.type_check_expects(right, context, &TypeSignature::UIntType)?;

    Ok(seq)
}

/// This function type checks the Clarity2 function `replace-at?`.
pub fn check_special_replace_at(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> Result<TypeSignature, CheckError> {
    let [input, index, element] = get_arguments_exact(args)?;

    runtime_cost(ClarityCostFunction::AnalysisIterableFunc, checker, 0)?;
    // Check sequence
    let input_type = checker.type_check(input, context)?;
    let seq_type = match &input_type {
        TypeSignature::SequenceType(seq) => seq,
        _ => return Err(CheckErrors::ExpectedSequence(Box::new(input_type)).into()),
    };
    let unit_seq = seq_type.unit_type()?;
    // Check index argument
    checker.type_check_expects(index, context, &TypeSignature::UIntType)?;
    // Check element argument
    checker.type_check_expects(element, context, &unit_seq)?;

    let final_type = TypeSignature::new_option(input_type)?;
    Ok(final_type)
}
