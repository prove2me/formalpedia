-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_second_block_gcd_cases
-- name    : OddPerfectNumber.Kernel.second_block_gcd_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T02:29:11.913826+00:00
-- url     : https://prove2.me/theorems/f4a084d9-cd5d-4795-8507-73b044f7001d
-- title:
--   The gcd of (p+1)/2 and p^2-p+1 is 1 or 3 when p = 1 mod 4
-- statement:
--   For every natural $p$ with $p \equiv 1 \pmod 4$, the greatest common divisor of $\frac{p+1}{2}$ and $p^2-p+1$ is either $1$ or $3$. This is exactly the case split that the proved child `second_block_gcd_dvd_three` (0e45b51d) leaves open: that child gives only the divisibility $\gcd\;(\tfrac{p+1}{2})\,(p^2-p+1) \mid 3$, and since $3$ is prime a positive divisor of $3$ is $1$ or $3$. The $1$ branch is the coprime case used to force $p^2-p+1$ to be a square; the $3$ branch is the branch in which $p^2-p+1$ is three times a square, contradicted by `quad_not_three_mul_sq` (47b149df). Making the split an explicit child removes the only genuinely reusable step of the parent proof.
-- source:
--   Odd Perfect Number Conjecture, $k=5$ branch, hp4 product-nonsquare chain. Purely elementary: it is the finitisation of the accepted divisibility child `OddPerfectNumber.Kernel.second_block_gcd_dvd_three` (0e45b51d-915a-4c31-bec6-b2f945374870) via `Nat.dvd_prime Nat.prime_three`. No new mathematics and no deep input.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem second_block_gcd_cases (p : Nat) (hp4 : p % 4 = 1) :
    Nat.gcd ((p + 1) / 2) (p ^ 2 - p + 1) = 1 ∨
      Nat.gcd ((p + 1) / 2) (p ^ 2 - p + 1) = 3 := by
  sorry

end OddPerfectNumber.Kernel
