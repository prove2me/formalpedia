-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_lob_v2
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_lob_v2
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-18T04:59:18.497376+00:00
-- url     : https://prove2.me/theorems/e6cf4251-df11-42c2-933f-b313e909574d
-- title:
--   q3=29 b=1 D enumeration lob v2
-- statement:
--   Smooth D in [28,43] with 2D-1 prime (v2).
-- source:
--   V2 republication to escape immutable snapshot holding CE bytes; proof uses try-wrapped staging.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_lob_v2 (D : Nat)
    (hlo : 28 ≤ D) (hhi : D ≤ 43)
    (hD3 : D % 3 = 0 ∨ D % 5 = 0 ∨ D % 29 = 0 ∨ D % 31 = 0)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
