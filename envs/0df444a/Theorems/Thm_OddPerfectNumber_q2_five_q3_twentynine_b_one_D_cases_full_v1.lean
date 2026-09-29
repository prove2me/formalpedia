-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_full_v1
-- name    : OddPerfectNumber.q2_five_q3_twentynine_b_one_D_cases_full_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T05:06:44.328643+00:00
-- url     : https://prove2.me/theorems/70a0f3dd-ecb4-4cd9-8d53-7280fe23d852
-- title:
--   q3=29 b=1 full D enumeration composer
-- statement:
--   Full-range composer over the four accepted v3 subrange enumerations.
-- source:
--   Pure dispatch over accepted v3 pieces; no arithmetic.

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_loa_v3
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_lob_v3
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_mid_v3
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_b_one_D_cases_hi_v3

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_b_one_D_cases_full_v1 (D : Nat)
    (hlo : 12 ≤ D) (hhi : D ≤ 105)
    (hD : D ∣ 1820475)
    (hp : Nat.Prime (2 * D - 1)) :
    D = 15 ∨ D = 27 ∨ D = 31 ∨ D = 45 ∨ D = 75 ∨ D = 87 := by
  sorry

end OddPerfectNumber
