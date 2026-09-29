-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_v1
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_v1
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-18T04:55:27.637026+00:00
-- url     : https://prove2.me/theorems/44dda9c0-6670-495d-8a84-87f50eb2d4ef
-- title:
--   q3=29 b=1 finite D enumeration
-- statement:
--   Smooth D in [12,105] with 2D-1 prime lies in {15,27,31,45,75,87}. Pure finite enumeration for the q29 b=1 route.
-- source:
--   Finite enumeration supporting the q29 b!=1 D<=105 reduction. Pure arithmetic, no sigma infrastructure.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_v1 (D : Nat)
    (hlo : 12 ≤ D) (hhi : D ≤ 105)
    (hD3 : D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
