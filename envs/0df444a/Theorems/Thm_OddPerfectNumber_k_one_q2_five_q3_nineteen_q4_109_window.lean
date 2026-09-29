-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_109_window
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_109_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T20:30:05.315376+00:00
-- url     : https://prove2.me/theorems/8a03ce9a-385d-4031-b24d-d1a9d2f20be3
-- title:
--   Canonical q3=19 q4=109 abundance window
-- statement:
--   Under the canonical q3=19 q4=109 large-D hypotheses, exact abundance bounds force 379 ≤ D ≤ 398.
-- source:
--   The q4=109 instance of the accepted exact abundance window calculation.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_109_window (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 225 ≤ D) (hp_eq : p = 2 * D - 1) (hq4 : q4 = 109) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : 379 ≤ D ∧ D ≤ 398 := by
  sorry

end OddPerfectNumber
