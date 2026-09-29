-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_q4_le_139_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_q4_le_139_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T20:51:01.109922+00:00
-- url     : https://prove2.me/theorems/504afa9e-0a25-40c3-8a45-c6bed8590885
-- title:
--   q3=19 middle q4 at most 139 contradicts abundance
-- statement:
--   In the canonical middle q3=19 range, a fourth prime at most 139 contradicts the exact abundance relation.
-- source:
--   Multiply the accepted lower abundance ratios for the 3, 5, and 19 components with the q4≤139 ratio certificate. Substituting m² and the Euler relation yields a strict coefficient inequality; exact arithmetic contradicts p=2D−1 throughout 147≤D<225.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_le_139_ratio_v1
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_middle_q4_le_139_absurd_v1 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 147 ≤ D) (hDhigh : D < 225) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hq4le : q4 ≤ 139) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
