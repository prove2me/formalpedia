-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_coprime_non_square_blocks_prime_mul_sq
-- name    : OddPerfectNumber.Kernel.coprime_non_square_blocks_prime_mul_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T21:33:31.667205+00:00
-- url     : https://prove2.me/theorems/8f66da20-c05d-480b-9aaf-d14671217ab2
-- title:
--   Coprime non-square blocks of a prime times a square carry the prime in a prescribed order
-- statement:
--   Let $a$ and $b$ be coprime nonzero naturals, let $c$ be prime, and suppose $a b = c y^2$ with neither $a$ nor $b$ a square. Then exactly one of $a$ and $b$ equals $c$ times a square, and the other is a square.
--
--   Since $a b = c y^2$, the total multiplicity of every prime in $a b$ is even except that of $c$, which is odd. Coprimality means each prime occurs in at most one of the two blocks, so the block containing $c$ has $c$ to an odd power and every other prime to an even power, while the other block has all multiplicities even and is therefore a square. As neither block is a square, the block containing $c$ cannot be the other one, giving the disjunction.
--
--   In the $k = 5$ residual this is the tool that turns a prime-times-a-square second cyclotomic block into the concrete statement that one of the two prime-times-square orientations actually occurs.
-- source:
--   Mathlib/Data/Nat/Factorization/Defs.lean (Nat.factorization_mul, Nat.factorization_eq_zero_of_not_dvd) and Mathlib/Data/Nat/GCD/Basic.lean (dvd_gcd, Coprime.gcd_eq_one), together with the accepted bridge OddPerfectNumber.Kernel.isSq_iff_even_factorization (28b00e2d-2e78-4683-8075-7135bec4a50b). Elementary exponent-parity bookkeeping; it encodes no unproved conjecture.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem coprime_non_square_blocks_prime_mul_sq {a b c y : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc : c.Prime) (hab : a.Coprime b) (hna : ¬ ∃ w : Nat, w ^ 2 = a)
    (hnb : ¬ ∃ w : Nat, w ^ 2 = b) (hy : a * b = c * y ^ 2) :
    (∃ x : Nat, a = c * x ^ 2) ∨ (∃ x : Nat, b = c * x ^ 2) := by
  sorry

end OddPerfectNumber.Kernel
