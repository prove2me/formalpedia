-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_loa_v1
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_loa_v1
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-18T04:57:18.151138+00:00
-- url     : https://prove2.me/theorems/a842293e-9df2-4cd3-a2f2-01b72bc9a80c
-- title:
--   q3=29 b=1 D enumeration loa
-- statement:
--   Smooth D in [12,27] with 2D-1 prime.
-- source:
--   Guard-safe split of lo chunk.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_loa_v1 (D : Nat)
    (hlo : 12 ≤ D) (hhi : D ≤ 27)
    (hD3 : D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
