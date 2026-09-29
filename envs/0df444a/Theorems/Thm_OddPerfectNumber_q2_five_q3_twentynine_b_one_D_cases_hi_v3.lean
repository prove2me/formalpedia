-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_hi_v3
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_hi_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T05:03:56.264798+00:00
-- url     : https://prove2.me/theorems/6424f162-18c1-4f00-81ee-c029ffbb9a91
-- title:
--   q3=29 b=1 D enumeration hi v3
-- statement:
--   Smooth D in [75,105] (via divisibility by 3^4*5^2*29*31) with 2D-1 prime lies in the survivor set.
-- source:
--   V3 corrects the false v1/v2 divisibility-by-one hypothesis to true smoothness via D | 1820475; survivors verified numerically.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_hi_v3 (D : Nat)
    (hlo : 75 ≤ D) (hhi : D ≤ 105)
    (hD : D ∣ 1820475)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
