use criterion::{black_box, criterion_group, criterion_main, Criterion};
use arm64_arith::*;
use rand::*;

fn b128(c: &mut Criterion) {
    let mut rng = thread_rng();
    let a: [u64; 2] = rng.gen();
    let b: [u64; 2] = rng.gen();

    c.bench_function("u128 wide mul", |bencher| bencher.iter(|| mul_assign(black_box(a), black_box(b))));
}

fn b128_arm(c: &mut Criterion) {
    let mut rng = thread_rng();
    let a: [u64; 2] = rng.gen();
    let b: [u64; 2] = rng.gen();

    c.bench_function("u128 wide mul", |bencher| bencher.iter(|| mul_assign_2(black_box(a), black_box(b))));
}

// fn b256(c: &mut Criterion) {
//     let mut rng = thread_rng();
//     let a: [u64; 4] = rng.gen();
//     let b: [u64; 4] = rng.gen();

//     c.bench_function("u256 wide mul", |bencher| bencher.iter(|| mul_assign_256(black_box(a), black_box(b))));
// }

// fn bm256(c: &mut Criterion) {
//     let mut rng = thread_rng();
//     let a: [u64; 4] = rng.gen();
//     let b: [u64; 4] = rng.gen();

//     c.bench_function("u256 mont mul", |bencher| bencher.iter(|| mont_mul_assign_256(black_box(a), black_box(b))));
// }

criterion_group!(benches, b128, b128_arm);
criterion_main!(benches);