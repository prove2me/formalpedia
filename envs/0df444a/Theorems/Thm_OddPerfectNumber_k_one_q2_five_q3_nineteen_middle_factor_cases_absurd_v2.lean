-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_factor_cases_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_factor_cases_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T21:38:00.224107+00:00
-- url     : https://prove2.me/theorems/275db4c5-0b8e-4742-9475-d074b48c7a7a
-- title:
--   q3=19 four middle factor tuples are abundant v2
-- statement:
--   Each of the four finite q3=19 middle tuples contradicts exact abundance using a concrete three-term q4 estimate.
-- source:
--   The changed proof keeps q4 concrete before normalizing the exact three-term estimate, then reuses one common abundance cancellation lemma.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_middle_factor_cases_absurd_v2 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hcases : (D = 159 ∧ q4 = 53 ∧ p = 317) ∨ (D = 177 ∧ q4 = 59 ∧ p = 353) ∨ (D = 201 ∧ q4 = 67 ∧ p = 401) ∨ (D = 205 ∧ q4 = 41 ∧ p = 409)) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
