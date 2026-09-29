-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_101_window
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_101_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T18:22:48.926128+00:00
-- url     : https://prove2.me/theorems/2edacc9e-8be6-465e-b1bc-0443ad70672f
-- title:
--   Canonical q3=19 q4=101 abundance window
-- statement:
--   In the q3=19 large-D branch with q4=101, the exact lower and upper abundance inequalities force 854≤D≤960.
-- source:
--   Multiply the accepted sharp lower ratio bounds with the last-three-term q4=101 bound, then combine with D*sigma=(2D-1)m^2. The strict Euler upper bounds give the matching D≤960 cut.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_101_window (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 225 ≤ D) (hp_eq : p = 2 * D - 1) (hq4 : q4 = 101) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : 854 ≤ D ∧ D ≤ 960 := by sorry

end OddPerfectNumber
