#![feature(asm)]
#![feature(unchecked_math)]

use std::os::unix::prelude::CommandExt;

const INV: u64 = 0xffffffffffffffff;

static ZERO_U64: u64 = 0;
static ONE_U64: u64 = 1;
static U64_MAX: u64 = 0xffffffffffffffff;

// static MODULUS_0_STATIC: u64 = 1;
static MODULUS_1_STATIC: u64 = 0x3000000300000001;

const MODULUS: [u64; 4] = [1, 0x3000000300000001, 0x3000000300000001, 0x3000000300000001];

// 2^256 - MODULUS
static MODULUS_NEGATED_STATIC_0: u64 = 0xffffffffffffffff;
static MODULUS_NEGATED_STATIC_1: u64 = 0xcffffffcfffffffe;

#[inline(always)]
pub const fn carrying_add(lhs: u64, rhs: u64, carry: bool) -> (u64, bool) {
    let (a, b) = lhs.overflowing_add(rhs);
    let (c, d) = a.overflowing_add(carry as u64);
    (c, b | d)
}

#[inline(always)]
pub fn add_propagate_carry(a: u64, b: u64, existing_high: u64) -> (u64, u64) {
    let (low, c) = a.overflowing_add(b);
    let high = unsafe {
        existing_high.unchecked_add(c as u64)
    };

    (low, high)
}

#[inline(always)]
pub const fn borrowing_sub(lhs: u64, rhs: u64, carry: bool) -> (u64, bool) {
    let (a, b) = lhs.overflowing_sub(rhs);
    let (c, d) = a.overflowing_sub(carry as u64);
    (c, b | d)
}

#[inline(always)]
pub fn widening_mul(lhs: u64, rhs: u64) -> (u64, u64) {
    let wide = unsafe {
        (lhs as u128).unchecked_mul(rhs as u128)
    };
    (wide as u64, (wide >> 64) as u64)
}

#[inline(always)]
pub fn carrying_mul(lhs: u64, rhs: u64, carry: u64) -> (u64, u64) {
    let wide = unsafe {
        (lhs as u128).unchecked_mul(rhs as u128).unchecked_add(carry as u128)
    };
    (wide as u64, (wide >> 64) as u64)
}

pub fn mul_assign(this: [u64; 2], other: [u64; 2]) -> [u64; 4] {
    // start all chains and let the CPU and compiler decide
    let a = this[0];
    let (r0, carry) = widening_mul(a, other[0]);
    let (r1, r2_0) = carrying_mul(a, other[1], carry);

    // ranges:
    // for any multiplication like (2^64 - 1) * (2^64 - 1) we can add something in the lowest limb
    // without overflow further then upper limb

    let a = this[1];
    let (r1, carry) = carrying_mul(a, other[0], r1);
    let (r2_1, r3_1) = carrying_mul(a, other[1], carry);

    // we have carried r1 initial value all the way, 
    // so now we need to carry something from r2

    // collapse r2 and then into r3
    let (r2, carry) = r2_0.overflowing_add(r2_1);
    let r3 = r3_1.wrapping_add(carry as u64);

    [r0, r1, r2, r3]

    // mont_reduce(r0, r1, r2, r3)
}

pub fn mul_assign_2(this: [u64; 2], other: [u64; 2]) -> [u64; 4] {
    // comba steps

    let (r0, t1, t2) = comba_mul_step(0, 0, 0, this[0], other[0]);
    let (t0, t1, t2) = comba_mul_step(t1, t2, 0, this[0], other[1]);
    let (r1, t1, t2) = comba_mul_step(t0, t1, t2, this[1], other[0]);
    let (r2, r3, _) = comba_mul_step(t1, t2, 0, this[1], other[1]);

    [r0, r1, r2, r3]
}


pub fn mul_assign_256(this: [u64; 4], other: [u64; 4]) -> [u64; 8] {
    // start all chains and let the CPU and compiler decide
    let a = this[0];
    let (r0, carry) = widening_mul(a, other[0]);
    let (r1, carry) = carrying_mul(a, other[1], carry);
    let (r2_0, carry) = carrying_mul(a, other[2], carry);
    let (r3_0, r4_0) = carrying_mul(a, other[3], carry);

    let a = this[1];
    let (r1, carry) = carrying_mul(a, other[0], r1);
    let (r2_1, carry) = carrying_mul(a, other[1], carry);
    let (r3_1, carry) = carrying_mul(a, other[2], carry);
    let (r4_1, r5_1) = carrying_mul(a, other[3], carry);

    // carry to get r2 capturable for this chain
    let (r2, carry) = r2_0.overflowing_add(r2_1);
    let (r3_i, carry) = carrying_add(r3_0, r3_1, carry);
    let (r4_i, carry) = carrying_add(r4_0, r4_1, carry);
    let r5_i = r5_1.wrapping_add(carry as u64);

    let a = this[2];
    let (r2, carry) = carrying_mul(a, other[0], r2);
    let (r3_2, carry) = carrying_mul(a, other[1], carry);
    let (r4_2, carry) = carrying_mul(a, other[2], carry);
    let (r5_2, r6_2) = carrying_mul(a, other[3], carry);

    // carry to get r3
    let (r3, carry) = r3_i.overflowing_add(r3_2);
    let (r4_i, carry) = carrying_add(r4_i, r4_2, carry);
    let (r5_i, carry) = carrying_add(r5_i, r5_2, carry);
    let r6_i = r6_2.wrapping_add(carry as u64);

    let a = this[3];
    let (r3, carry) = carrying_mul(a, other[0], r3);
    let (r4_3, carry) = carrying_mul(a, other[1], carry);
    let (r5_3, carry) = carrying_mul(a, other[2], carry);
    let (r6_3, r7_3) = carrying_mul(a, other[3], carry);

    // final carry
    let (r4, carry) = r4_i.overflowing_add(r4_3);
    let (r5, carry) = carrying_add(r5_i, r5_3, carry);
    let (r6, carry) = carrying_add(r6_i, r6_3, carry);
    let r7 = r7_3.wrapping_add(carry as u64);

    [r0, r1, r2, r3, r4, r5, r6, r7]
}

pub fn mont_mul_assign_256(this: [u64; 4], other: [u64; 4]) -> [u64; 4] {
    // cios and let compiler decide
    let mut t = [0u64; 6];
    for a in std::array::IntoIter::new(this) {
        let mut carry = 0;
        for (j, b) in std::array::IntoIter::new(other).enumerate() {
            let (tmp, c) = carrying_mul(a, b, t[j]);
            let (s, c) = add_propagate_carry(tmp, carry, c);
            t[j] = s;
            carry = c;
        }
        let (s, c) = t[4].overflowing_add(carry);
        t[4] = s;
        t[5] = c as u64;
        
        let m = t[0].wrapping_mul(INV);
        let (_, c) = carrying_mul(m, MODULUS[0], t[0]);
        carry = c;
        for j in 1..4 {
            let (tmp, c) = carrying_mul(m, MODULUS[j], t[j]);
            let (s, c) = add_propagate_carry(tmp, carry, c);
            t[j-1] = s;
            carry = c;
        }
        let (s, c) = t[4].overflowing_add(carry);
        t[3] = s;
        t[4] = t[5].wrapping_add(c as u64);
    }

    [t[0], t[1], t[2], t[3]]
}
    

// #[inline(always)]
// fn mont_reduce(
//     r0: u64,
//     mut r1: u64,
//     mut r2: u64,
//     mut r3: u64,
// ) -> [u64; 2]
// {
//     // The Montgomery reduction here is based on Algorithm 14.32 in
//     // Handbook of Applied Cryptography
//     // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

//     let k = r0.wrapping_mul(INV);
//     let mut carry = 0;
//     mac_with_carry(r0, k, MODULUS[0], &mut carry);
//     r1 = mac_with_carry(r1, k, MODULUS[1], &mut carry);
//     r2 = adc(r2, 0, &mut carry);
//     let carry2 = carry;
//     let k = r1.wrapping_mul(INV);
//     let mut carry = 0;
//     mac_with_carry(r1, k, MODULUS[0], &mut carry);
//     r2 = mac_with_carry(r2, k, MODULUS[1], &mut carry);
//     r3 = adc(r3, carry2, &mut carry);
    
//     [r2, r3]
// }

/// Calculate a + (b * c) + carry, returning the least significant digit
/// and setting carry to the most significant digit.
pub fn mac_with_carry_2(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let wide = unsafe {
        (b as u128).unchecked_mul(c as u128).unchecked_add(a as u128)
    };
    let wide = unsafe {
        wide.unchecked_add(*carry as u128)
    };

    *carry = (wide >> 64) as u64;

    wide as u64
}

pub fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (u128::from(a)).wrapping_add(u128::from(b).wrapping_mul(u128::from(c))).wrapping_add(u128::from(*carry));

    *carry = (tmp >> 64) as u64;

    tmp as u64
}

pub fn mac_with_carry_32(a: u32, b: u32, c: u32, carry: &mut u32) -> u32 {
    let tmp = (u64::from(a)).wrapping_add(u64::from(b).wrapping_mul(u64::from(c))).wrapping_add(u64::from(*carry));

    *carry = (tmp >> 32) as u32;

    tmp as u32
}

pub fn mac_with_carry_32_2(a: u32, b: u32, c: u32, d: u32) -> (u32, u32) {
    let wide = unsafe {
        (c as u64).unchecked_add(d as u64).unchecked_add((a as u64).unchecked_mul(b as u64))
    };

    (wide as u32, (wide >> 32) as u32) 
}

pub fn comba_mul_step(r0: u64, r1: u64, r2: u64, a: u64, b: u64) -> (u64, u64, u64) {
    let wide = unsafe {
        (a as u128).unchecked_mul(b as u128)
    };
    let (low, high) = (wide as u64, (wide >> 64) as u64);
    let (r0, carry_0) = r0.overflowing_add(low);
    let (r1, carry_1_0) = r1.overflowing_add(high);
    let (r1, carry_1_1) = r1.overflowing_add(carry_0 as u64);
    let r2 = r2.wrapping_add((carry_1_0 | carry_1_1) as u64);

    (r0, r1, r2)
}

pub fn test(a: [u32; 2], b: [u32; 2]) -> [u32; 4] {
    let (r0, r1) = mac_with_carry_32_2(a[0], b[0], 0, 0);
    let (r1, r2_0) = mac_with_carry_32_2(a[0], b[1], r1, 0);

    let (r1, r2_1) = mac_with_carry_32_2(a[1], b[0], r1, 0);
    let (r2, r3) = mac_with_carry_32_2(a[1], b[1], r2_0, r2_1);

    [r0, r1, r2, r3]
}

pub fn test2(a: [u32; 2], b: [u32; 2]) -> [u32; 4] {
    let mut carry = 0u32;
    let r0 = mac_with_carry_32(0, a[0], b[0], &mut carry);
    let r1 = mac_with_carry_32(0, a[0], b[1], &mut carry);

    let mut carry2 = 0u32;
    let r1 = mac_with_carry_32(r1, a[1], b[0], &mut carry2);
    let r2 = mac_with_carry_32(carry, a[1], b[1], &mut carry2);
    let r3 = carry2;

    [r0, r1, r2, r3]
}