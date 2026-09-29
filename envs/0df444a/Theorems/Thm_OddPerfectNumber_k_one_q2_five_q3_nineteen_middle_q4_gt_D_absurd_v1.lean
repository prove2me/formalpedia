-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_middle_q4_gt_D_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_q4_gt_D_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T20:23:41.384246+00:00
-- url     : https://prove2.me/theorems/788f778e-a9a3-4e49-b4d3-b395dafc9507
-- title:
--   q3=19 middle range with q4 greater than D is impossible
-- statement:
--   For 147≤D<225 and q4>D, the strict product upper bound for the four geometric sigma factors contradicts the Euler relation.
-- source:
--   Multiply the four strict scaled geometric-sum bounds to obtain 144*(q4-1)*sigma < 285*q4*m^2. The Euler relation gives the strict coefficient inequality 144*(q4-1)*(2D-1) < 285*q4*D, while D≥147 and q4>D make its reverse inequality hold by exact finite normalization.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_middle_q4_gt_D_absurd_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 147 ≤ D) (hDlt : D < 225)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (hq4gtD : D < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
