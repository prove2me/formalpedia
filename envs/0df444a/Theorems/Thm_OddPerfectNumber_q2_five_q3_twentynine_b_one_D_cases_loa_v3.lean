-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_loa_v3
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_loa_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T05:03:54.488728+00:00
-- url     : https://prove2.me/theorems/1daaad12-0f09-470f-80b9-913fa1d0f6f1
-- title:
--   q3=29 b=1 D enumeration loa v3
-- statement:
--   Smooth D in [12,27] (via divisibility by 3^4*5^2*29*31) with 2D-1 prime lies in the survivor set.
-- source:
--   V3 corrects the false v1/v2 divisibility-by-one hypothesis to true smoothness via D | 1820475; survivors verified numerically.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_loa_v3 (D : Nat)
    (hlo : 12 ≤ D) (hhi : D ≤ 27)
    (hD : D ∣ 1820475)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
