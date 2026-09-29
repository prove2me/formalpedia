-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_prime_pow_even
-- name    : OddPerfectNumber.sigma_prime_pow_even
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T08:25:46.645263+00:00
-- url     : https://prove2.me/theorems/474231ca-45f3-455d-8ca0-aa368d0b958f
-- title:
--   The divisor sum sigma(p^k) is even for odd p and k = 1 mod 4
-- statement:
--   Let $p$ be an odd prime and let $k \equiv 1 \pmod 4$. Then the sum-of-divisors function at $p^k$, $$\sigma(p^k) = 1 + p + \cdots + p^k,$$ is even. Since $k + 1 \equiv 2 \pmod 4$, the number of terms $k+1$ is even, and every term is odd, so their sum is even. This is the uniform 2-adic entry point for the Dris-index analysis at every admissible special exponent: writing $$\sigma(p^k) = 2t$$ lets the relation $2m^2 = \sigma(p^k)s$ cancel to $m^2 = ts$. It subsumes the instances $k = 1, 5, 9, 13, \ldots$.
-- source:
--   Dris-index analysis of the Odd Perfect Number Conjecture at special exponent k = 1 mod 4; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem sigma_prime_pow_even (p k : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk4 : k % 4 = 1) : Even (∑ d ∈ (p ^ k).divisors, d) := by
  sorry

end OddPerfectNumber
