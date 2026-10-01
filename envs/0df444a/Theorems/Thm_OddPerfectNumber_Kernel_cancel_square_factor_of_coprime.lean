-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_cancel_square_factor_of_coprime
-- name    : OddPerfectNumber.Kernel.cancel_square_factor_of_coprime
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T22:34:00.028977+00:00
-- url     : https://prove2.me/theorems/c52ea1ab-1cf3-466a-8b25-bc355193498c
-- title:
--   Cancelling a coprime prime times a square factor forces the other factor to be a square
-- statement:
--   Let $a, b$ be coprime nonzero naturals, $c$ prime, and suppose $a = c x^2$ and $a b = c y^2$. Then $b$ is a perfect square.
--
--   Indeed $a$ and $c$ are coprime (primality of $c$ and coprimality of $a$ and $b$ force $c \nmid a$ only if $c$ sits in one block; equivalently the odd multiplicity of $c$ in $a$ is cancelled exactly once), so substituting gives $c x^2 b = c y^2$, hence $x^2 b = y^2$ and $b = (y/x)^2$. This is the cancellation step that turns a prime-times-a-square identification of one block into a square statement about the other.
--
--   The $k = 5$ residual uses it in both orientations of the second cyclotomic block, and it is the exact tool that repairs the `gcd = 1` branch of `second_block_first_half_sq_or_three_sq` after the unprimed helper `coprime_prime_mul_sq_has_square_side` (c70263a1) was Disproved.
-- source:
--   Mathlib/Data/Nat/GCD/Basic.lean (dvd_gcd, Coprime.gcd_eq_one) and Mathlib/Data/Nat/Factorization/Defs.lean, together with the accepted bridge OddPerfectNumber.Kernel.isSq_iff_even_factorization (28b00e2d-2e78-4683-8075-7135bec4a50b) and the accepted OddPerfectNumber.Kernel.coprime_sq_factor_right (da2991de). Elementary exponent-parity bookkeeping; it encodes no unproved conjecture.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem cancel_square_factor_of_coprime {a b c x y : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc : c.Prime) (hab : a.Coprime b) (hax : a = c * x ^ 2) (hy : a * b = c * y ^ 2) :
    exists z : Nat, z ^ 2 = b := by
  sorry

end OddPerfectNumber.Kernel
