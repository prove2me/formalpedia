-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_five_s_odd_ge_five
-- name    : OddPerfectNumber.no_dris_five_s_odd_ge_five
-- status  : Open
-- author  : @WillR
-- created : 2026-09-11T06:02:06.982395+00:00
-- url     : https://prove2.me/theorems/d9cb6492-56f9-4937-a524-5c3389548589
-- title:
--   Dris-index case s >= 5 with s odd is impossible
-- statement:
--   Let $p$ be an odd prime with $p \equiv 1 \pmod 4$, let $m$ be odd with $p \nmid m$, and let $s \ge 5$ be odd. Then the two Dris relations $2m^2 = \sigma(p^5)s$ and $\sigma(m^2) = p^5s$ cannot both hold. This is the large-index remainder of the odd-$s$ Dris problem for special exponent $k = 5$ after the index-three case is split off.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation of the Euler equation); Euler form and special-exponent case k = 5 as recorded on the Odd Perfect Number Conjecture mission.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_five_s_odd_ge_five (p m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs_not_even : ¬ Even s)
    (hs5 : 5 ≤ s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  sorry

end OddPerfectNumber
