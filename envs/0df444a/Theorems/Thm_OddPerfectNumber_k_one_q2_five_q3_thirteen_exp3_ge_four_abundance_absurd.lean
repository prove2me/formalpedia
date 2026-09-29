-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp3_ge_four_abundance_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_exp3_ge_four_abundance_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:45:41.921563+00:00
-- url     : https://prove2.me/theorems/a967387f-1ac7-47dd-8580-620cd054f968
-- title:
--   The exponent-four-or-larger 3-component exceeds abundance in the q2=5 q3=13 branch
-- statement:
--   With a≥4 and the other support exponents at least two, the exact lower abundance certificate contradicts sigma≤2m².
-- source:
--   Finite abundance certificate for the q2=5, q3=13 branch.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_four
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_exp3_ge_four_abundance_absurd (m a b c e q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 13 ^ c * q4 ^ e)
    (hsigma : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (ha : 4 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hq : q4 ^ e ≤ ∑ i ∈ Finset.range (e + 1), q4 ^ i) :
    False := by
  sorry

end OddPerfectNumber
