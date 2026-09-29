-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_nine_even_of_odd_prime
-- name    : OddPerfectNumber.sigma_nine_even_of_odd_prime
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T08:22:18.553464+00:00
-- url     : https://prove2.me/theorems/24d3b2d7-fb91-415e-9f6c-ba9fb492b800
-- title:
--   The divisor sum sigma(p^9) is even for odd prime p
-- statement:
--   Let $p$ be an odd prime. Then the sum-of-divisors function at $p^9$, $$\sigma(p^9) = 1 + p + \cdots + p^9,$$ is even. Each of the ten terms is odd, so their sum is even. This is the 2-adic entry point for the Dris-index analysis at special exponent $k = 9$: writing $$\sigma(p^9) = 2t$$ lets the relation $2m^2 = \sigma(p^9)s$ cancel to $m^2 = ts$.
-- source:
--   Dris-index analysis of the special-exponent k = 9 case of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem sigma_nine_even_of_odd_prime (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    Even (∑ d ∈ (p ^ 9).divisors, d) := by
  sorry

end OddPerfectNumber
