-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_one_odd_prime_core
-- name    : OddPerfectNumber.no_dris_one_odd_prime_core
-- status  : Open
-- author  : @WillR
-- created : 2026-09-11T09:19:19.729654+00:00
-- url     : https://prove2.me/theorems/c2eb54d0-36ad-490e-98cf-f6496063673e
-- title:
--   Cleaned one-odd-prime residual core is impossible
-- statement:
--   Let $p$ be prime, $k \neq 0$ with $k+1$ having at most one odd prime factor, $m$ odd with $p \nmid m$, and $s \geq 2$ composite and not even with $s \mid m^2$. Then the Dris packaged identities $2m^2 = \sigma(p^k) \cdot s$ and $\sigma(m^2) = p^k \cdot s$ are jointly impossible. This is the cleaned research core of the one-odd-prime residual after the elementary cofactor-divisibility packaging.
-- source:
--   Dris cofactor analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem no_dris_one_odd_prime_core (p k m s : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) (hs_not_prime : ¬ s.Prime)
    (hs_dvd : s ∣ m ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
