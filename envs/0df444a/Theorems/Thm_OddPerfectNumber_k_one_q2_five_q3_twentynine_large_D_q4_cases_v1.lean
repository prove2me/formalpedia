-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_cases_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_cases_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T10:30:41.894076+00:00
-- url     : https://prove2.me/theorems/00f00326-4d43-4321-8e01-682462bacc85
-- title:
--   Canonical q3=29 large-D fourth-prime cases
-- statement:
--   A prime fourth support between 30 and 43 is one of 31, 37, 41, or 43.
-- source:
--   Exact finite prime enumeration after the accepted q3=29 large-D upper cut.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_large_D_q4_cases_v1 (q4 : Nat) (hq4prime : q4.Prime) (hq4gt : 29 < q4) (hq4le : q4 ≤ 43) : q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 := by
  sorry

end OddPerfectNumber
