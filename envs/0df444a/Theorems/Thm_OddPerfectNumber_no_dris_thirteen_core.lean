-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_thirteen_core
-- name    : OddPerfectNumber.no_dris_thirteen_core
-- status  : Open
-- author  : @WillR
-- created : 2026-09-11T09:17:18.786952+00:00
-- url     : https://prove2.me/theorems/879ca6cf-9ae2-4a3a-9c92-b397f00a2be3
-- title:
--   Cleaned thirteen-residual core is impossible
-- statement:
--   Let $p$ be an odd prime with $p \equiv 1 \pmod 4$, $k \geq 13$ with $k \equiv 1 \pmod 4$ such that $k+1$ has at least two odd prime factors, $m$ odd with $p \nmid m$, and $s \geq 2$ not even with $s \mid m^2$. Then the Dris packaged identities $2m^2 = \sigma(p^k) \cdot s$ and $\sigma(m^2) = p^k \cdot s$ are jointly impossible. This is the cleaned research core of the thirteen-residual after the elementary cofactor-divisibility packaging.
-- source:
--   Dris cofactor analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem no_dris_thirteen_core (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s)
    (hk1 : 2 ≤ ((k + 1).primeFactors.erase 2).card)
    (hs_dvd : s ∣ m ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
