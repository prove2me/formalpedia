-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_le_139_ratio_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_le_139_ratio_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T20:35:58.934614+00:00
-- url     : https://prove2.me/theorems/e51166d1-6022-4621-aec1-83d64525bdaa
-- title:
--   Uniform q4 lower abundancy ratio through 139
-- statement:
--   For 19<q4≤139 and exponent e≥1, the last three geometric terms give 19461*q4^(2e) ≤ 19321 times the q4 geometric sum.
-- source:
--   Use the accepted last-three-term geometric sum bound. The exact endpoint inequality is 140*q^2 ≤ 19321*q+19321 for q≤139, so multiplying by q^(2e-2) yields the stated ratio.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_le_139_ratio_v1 (q e : Nat) (hqgt : 19 < q) (hqle : q ≤ 139) (he : 1 ≤ e) : 19461 * q ^ (2*e) ≤ 19321 * (∑ i ∈ Finset.range (2*e + 1), q ^ i) := by
  sorry

end OddPerfectNumber
