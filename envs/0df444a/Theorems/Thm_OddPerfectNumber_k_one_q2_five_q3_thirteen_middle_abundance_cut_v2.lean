-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_abundance_cut_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T01:42:12.584586+00:00
-- url     : https://prove2.me/theorems/1d422862-380f-4bd2-835e-98a1a62c381f
-- title:
--   The nine low-q4 q3=13 middle candidates violate abundance
-- statement:
--   The nine q3=13 middle candidates with q4≤47 contradict the exact canonical abundance relation using the accepted geometric lower bounds.
-- source:
--   Multiply exact lower bounds 13/9, 3906/3125, 183/169, and 48/47 for the four local geometric sums. The resulting ratio is strictly above p/D for each of the nine displayed tuples, contradicting D·sigma=p·m².

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_two_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_base_le47

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_middle_abundance_cut_v2
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hcases :
      (D = 51 ∧ p = 101 ∧ q4 = 17) ∨
      (D = 57 ∧ p = 113 ∧ q4 = 19) ∨
      (D = 69 ∧ p = 137 ∧ q4 = 23) ∨
      (D = 87 ∧ p = 173 ∧ q4 = 29) ∨
      (D = 115 ∧ p = 229 ∧ q4 = 23) ∨
      (D = 129 ∧ p = 257 ∧ q4 = 43) ∨
      (D = 141 ∧ p = 281 ∧ q4 = 47) ∨
      (D = 187 ∧ p = 373 ∧ q4 = 17) ∨
      (D = 205 ∧ p = 409 ∧ q4 = 41))
    (hq4prime : q4.Prime) (hq4le : q4 ≤ 47)
    (ha : 2 ≤ a) (hb : 8 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
