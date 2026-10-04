-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_second_block_first_half_sq_or_three_sq
-- name    : OddPerfectNumber.Kernel.second_block_first_half_sq_or_three_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T18:56:32.246368+00:00
-- url     : https://prove2.me/theorems/a8a4da03-234a-4c76-9155-c5c7d8a787d5
-- title:
--   If the second cyclotomic block is a prime times a square, its first factor is a square or three times a square
-- statement:
--   Let $p$ be a prime with $p \equiv 1 \pmod 4$ and put $A = (p+1)/2$, $B = p^2-p+1$. If the product $A B$ is a prime $c$ times a perfect square, then $A$ is either a perfect square or three times a perfect square.
--
--   Indeed the accepted child OddPerfectNumber.Kernel.second_block_gcd_dvd_three (0e45b51d) gives $\gcd A B \mid 3$, so the only prime that can divide both blocks is $3$. The square relation $A B = c y^2$ says that exactly one prime, namely $c$, occurs to odd multiplicity in $A B$. Because the odd multiplicities of $A$ and $B$ multiply to $c$, precisely one of the two blocks is a square. The block $B$ cannot be a square, since $(p-1)^2 < p^2-p+1 < p^2$ for $p > 1$. Hence $A$ carries all the odd multiplicity, and since the only prime that may be shared is $3$, the odd-multiplicity prime of $A$ is $c$ and dividing $A$ by the possible single factor $3$ leaves a square. This is the elementary shape forced on the first factor of the second cyclotomic block whenever the block is a prime times a square; it is the arithmetic content of the $k=5$ two-prime residual.
-- source:
--   Mathlib/Data/Nat/Factorization/Defs.lean (Nat.factorization_mul, Nat.factorization_eq_zero_of_not_dvd) and Mathlib/Data/Nat/GCD/Basic.lean, together with the accepted children OddPerfectNumber.Kernel.second_block_gcd_dvd_three (0e45b51d-915a-4c31-bec6-b2f945374870) and OddPerfectNumber.Kernel.coprime_sq_factor_right. The interval non-square fact for $p^2-p+1$ is the second component of the accepted OddPerfectNumber.Kernel.five_cyclotomic_factors_ne_square (648a7dc4). Elementary exponent-parity bookkeeping plus gcd control by 3; it encodes no unproved conjecture.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem second_block_first_half_sq_or_three_sq (p c y : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hc : c.Prime) (hy : ((p + 1) / 2) * (p ^ 2 - p + 1) = c * y ^ 2) :
    (exists z : Nat, (p + 1) / 2 = z ^ 2) ∨ (exists z : Nat, (p + 1) / 2 = 3 * z ^ 2) := by
  sorry

end OddPerfectNumber.Kernel
