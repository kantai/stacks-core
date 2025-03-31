#[cfg(not(any(target_os = "macos", target_os = "windows", target_arch = "arm")))]
use tikv_jemallocator::Jemalloc;

#[cfg(not(any(target_os = "macos", target_os = "windows", target_arch = "arm")))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

fn main() {
    stacks_node::entry_main();
}
