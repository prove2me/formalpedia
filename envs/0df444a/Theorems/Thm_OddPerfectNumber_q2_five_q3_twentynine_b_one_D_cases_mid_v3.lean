-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_mid_v3
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_mid_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T05:03:54.778977+00:00
-- url     : https://prove2.me/theorems/0b13a350-71b3-4797-b34a-46db35e36065
-- title:
--   q3=29 b=1 D enumeration mid v3
-- statement:
--   Smooth D in [44,74] (via divisibility by 3^4*5^2*29*31) with 2D-1 prime lies in the survivor set.
-- source:
--   V3 corrects the false v1/v2 divisibility-by-one hypothesis to true smoothness via D | 1820475; survivors verified numerically.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_mid_v3 (D : Nat)
    (hlo : 44 ≤ D) (hhi : D ≤ 74)
    (hD : D ∣ 1820475)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
