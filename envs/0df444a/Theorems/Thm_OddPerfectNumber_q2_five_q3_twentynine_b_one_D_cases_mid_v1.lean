-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_mid_v1
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_mid_v1
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-18T04:56:27.842047+00:00
-- url     : https://prove2.me/theorems/deeb2a1a-c57b-422b-8452-b53660723f29
-- title:
--   q3=29 b=1 D enumeration mid
-- statement:
--   Smooth D in [44,74] with 2D-1 prime lies in the b=1 survivor set.
-- source:
--   Split of the b=1 D enumeration to satisfy the interval-case static guard.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_mid_v1 (D : Nat)
    (hlo : 44 ≤ D) (hhi : D ≤ 74)
    (hD3 : D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
