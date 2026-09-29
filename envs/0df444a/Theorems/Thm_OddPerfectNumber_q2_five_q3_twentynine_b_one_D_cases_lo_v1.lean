-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_lo_v1
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_lo_v1
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-18T04:56:28.875478+00:00
-- url     : https://prove2.me/theorems/65d4d2f8-1b27-44cb-af8b-8966b454f56a
-- title:
--   q3=29 b=1 D enumeration lo
-- statement:
--   Smooth D in [12,43] with 2D-1 prime lies in the b=1 survivor set.
-- source:
--   Split of the b=1 D enumeration to satisfy the interval-case static guard.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_lo_v1 (D : Nat)
    (hlo : 12 ≤ D) (hhi : D ≤ 43)
    (hD3 : D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
