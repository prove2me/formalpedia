-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_five_s_ge_two_even
-- name    : OddPerfectNumber.no_dris_five_s_ge_two_even
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-10T22:27:05.873542+00:00
-- url     : https://prove2.me/theorems/4069db3d-e442-4b2a-b113-4636d3aa70f3
-- title:
--   Dris-index case s ge 2 with s even is impossible
-- statement:
--   Let p be an odd prime with p congruent 1 mod 4, let m be odd with p not dividing m, and let s >= 2 be even. Then the two Dris relations 2m^2 = sigma(p^5)s and sigma(m^2) = p^5 s cannot both hold. This is the even-s half of the s >= 2 Dris-index problem for special exponent k = 5.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_five_s_ge_two_even (p m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs : 2 ≤ s) (hs_even : Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  sorry

end OddPerfectNumber
