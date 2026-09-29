-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_le_141_ratio_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_le_141_ratio_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T17:39:07.068607+00:00
-- url     : https://prove2.me/theorems/b0770f42-80a8-4926-a438-864236379f45
-- title:
--   Uniform q4 lower abundancy ratio through 141
-- statement:
--   For q between 20 and 141 and an even exponent at least two, the last three terms of the geometric sum give the cross-multiplied lower ratio 20023/19881.
-- source:
--   The exact factorization (141-q)(142q+141) turns the accepted last-three-terms bound into the uniform lower ratio.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_q4_le_141_ratio_v1 (q e : Nat) (hqgt : 19 < q) (hqle : q ≤ 141) (he : 1 ≤ e) :
    20023 * q ^ (2*e) ≤
      19881 * (∑ i ∈ Finset.range (2*e + 1), q ^ i) := by
  sorry

end OddPerfectNumber
