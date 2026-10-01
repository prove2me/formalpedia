-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_coprime_prime_mul_sq_has_square_side
-- name    : OddPerfectNumber.Kernel.coprime_prime_mul_sq_has_square_side
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-30T21:52:24.169794+00:00
-- url     : https://prove2.me/theorems/c70263a1-aaa4-4c96-9fdb-3041ca58b6f2
-- title:
--   Coprime factors of a prime times a square: one side is a square
-- statement:
--   Let $a$ and $b$ be coprime nonzero naturals with $a b = c y^2$. Then at least one of $a$ and $b$ is a perfect square.
--
--   Coprimality confines every prime to a single block, so the odd multiplicity of $c$ sits in exactly one block while the other block has all multiplicities even and is therefore a square. This is the coprime companion of the accepted `coprime_sq_factor_right` (da2991de), which handles the case where the product is itself a square; here one prime factor is left over, and exactly one side absorbs it.
--
--   The $k = 5$ residual uses this to force the first factor of the second cyclotomic block to be a square whenever the two blocks are coprime.
-- source:
--   Mathlib/Data/Nat/Factorization/Defs.lean (Nat.factorization_mul, Nat.factorization_eq_zero_of_not_dvd) and Mathlib/Data/Nat/GCD/Basic.lean (dvd_gcd, Coprime.gcd_eq_one), together with the accepted bridge OddPerfectNumber.Kernel.isSq_iff_even_factorization (28b00e2d-2e78-4683-8075-7135bec4a50b). Elementary exponent-parity bookkeeping; it encodes no unproved conjecture.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem coprime_prime_mul_sq_has_square_side {a b c y : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : a.Coprime b) (hy : a * b = c * y ^ 2) :
    (∃ z : Nat, z ^ 2 = a) \/ (∃ z : Nat, z ^ 2 = b) := by
  sorry

end OddPerfectNumber.Kernel
