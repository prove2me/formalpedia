-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_five_s_odd_eq_three
-- name    : OddPerfectNumber.no_dris_five_s_odd_eq_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T06:01:46.533437+00:00
-- url     : https://prove2.me/theorems/ca1ee4e5-7fac-42cc-9252-720f59a9eefd
-- title:
--   Dris-index case s = 3 with s odd is impossible
-- statement:
--   Let $p$ be an odd prime with $p \equiv 1 \pmod 4$, let $m$ be odd with $p \nmid m$, and fix the Dris index $s = 3$. Then the two Dris relations $2m^2 = \sigma(p^5)s$ and $\sigma(m^2) = p^5s$ cannot both hold. This is the index-three subcase of the odd-$s$ Dris problem for special exponent $k = 5$: writing $m = 3^a n$ with $3 \nmid n$ turns each admissibility level into a finite factor-and-check problem for $\sigma(3^{2a})$, cornered further by LTE/Zsigmondy constraints on the $3$-adic valuation.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation of the Euler equation); Euler form and special-exponent case k = 5 as recorded on the Odd Perfect Number Conjecture mission.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_five_s_odd_eq_three (p m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs3 : s = 3) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  sorry

end OddPerfectNumber
