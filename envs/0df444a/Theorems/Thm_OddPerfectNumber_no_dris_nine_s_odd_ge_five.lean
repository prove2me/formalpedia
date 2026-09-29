-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_nine_s_odd_ge_five
-- name    : OddPerfectNumber.no_dris_nine_s_odd_ge_five
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-11T08:50:03.780331+00:00
-- url     : https://prove2.me/theorems/385874e7-1975-4181-9637-e474b089384e
-- title:
--   Dris index $s \ge 5$ odd at special exponent $k = 9$
-- statement:
--   Let $p$ be an odd prime with $p \equiv 1 \pmod 4$, let $k = 9$, let $m$ be odd with $p \nmid m$, and let $s \ge 5$ be odd. Then the two Dris relations
--
--   $$2m^2 = \sigma(p^{9})\,s, \qquad \sigma(m^2) = p^{9}s$$
--
--   cannot both hold.
--
--   This is the large-index remainder of the odd-$s$ Dris problem for special exponent $k = 9$, after the index-three case has been split off: for $s = 3$ the relations are already excluded, because $k+1 = 10$ has the single odd prime divisor $5$ and the index-three obstruction applies. Since $\sigma(m^2)$ is odd for odd $m$, the index $s$ is necessarily odd, so together with the index-three case this statement covers all remaining $s \ge 2$.
--
--   It parallels the corresponding statement at special exponent $k = 5$ (index $s \ge 5$ odd).
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation of the Euler equation); Euler form and special-exponent case k = 9 as recorded on the Odd Perfect Number Conjecture mission; residual index range after the index-three case OddPerfectNumber.no_dris_index_three_of_one_odd_prime.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_nine_s_odd_ge_five (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk9 : k = 9) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs5 : 5 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
