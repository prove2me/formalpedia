-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_hi_v2
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_hi_v2
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-18T05:01:38.776209+00:00
-- url     : https://prove2.me/theorems/293f0d31-1d13-48f5-8004-02b8d67b9bc2
-- title:
--   q3=29 b=1 D enumeration hi v2
-- statement:
--   Smooth D in [75,105] with 2D-1 prime (v2).
-- source:
--   V2 republication; proof stages norm_num per hypothesis.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_hi_v2 (D : Nat)
    (hlo : 75 ≤ D) (hhi : D ≤ 105)
    (hD3 : D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
