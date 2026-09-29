-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_le_135_ratio_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_le_135_ratio_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T17:30:33.11266+00:00
-- url     : https://prove2.me/theorems/f71c09d6-2bab-4847-a37f-9b135068e44d
-- title:
--   Uniform q4 lower abundancy ratio through 135
-- statement:
--   For q between 20 and 135 and an even exponent at least two, the last three terms of the geometric sum give the cross-multiplied lower ratio 18361/18225.
-- source:
--   The exact factorization (135-q)(136q+135) turns the accepted last-three-terms bound into the uniform lower ratio.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_le_135_ratio_v1 (q e : Nat) (hqgt : 19 < q) (hqle : q ≤ 135) (he : 1 ≤ e) :
    18361 * q ^ (2*e) ≤
      18225 * (∑ i ∈ Finset.range (2*e + 1), q ^ i) := by
  sorry

end OddPerfectNumber
