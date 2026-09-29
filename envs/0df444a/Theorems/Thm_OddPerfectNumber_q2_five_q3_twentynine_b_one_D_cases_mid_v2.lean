-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_mid_v2
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_mid_v2
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-18T05:01:38.048955+00:00
-- url     : https://prove2.me/theorems/11f4f291-9fb2-40dd-a42b-82dea8eba640
-- title:
--   q3=29 b=1 D enumeration mid v2
-- statement:
--   Smooth D in [44,74] with 2D-1 prime (v2).
-- source:
--   V2 republication; proof stages norm_num per hypothesis.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_mid_v2 (D : Nat)
    (hlo : 44 ≤ D) (hhi : D ≤ 74)
    (hD3 : D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
