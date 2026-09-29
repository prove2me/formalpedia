-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_lob_v1
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_lob_v1
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-18T04:57:15.406416+00:00
-- url     : https://prove2.me/theorems/ccb085cd-c81e-45d8-82ce-9bd380362685
-- title:
--   q3=29 b=1 D enumeration lob
-- statement:
--   Smooth D in [28,43] with 2D-1 prime.
-- source:
--   Guard-safe split of lo chunk.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_lob_v1 (D : Nat)
    (hlo : 28 ≤ D) (hhi : D ≤ 43)
    (hD3 : D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
