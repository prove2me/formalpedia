-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_cases
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_q4_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T18:57:46.208527+00:00
-- url     : https://prove2.me/theorems/dfcade0a-d794-4772-b044-3c5a663a0ad7
-- title:
--   The q3=23 large-D fourth prime has three cases
-- statement:
--   A prime q4 strictly between 47 and 61 is exactly 53, 59, or 61.
-- source:
--   Exact finite prime enumeration after the accepted large-D bound q4≤61 and the minimum-abundance exclusion q4≤47.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_q4_cases (q4 : Nat)
    (hq4prime : q4.Prime) (hq4gt : 47 < q4) (hq4le : q4 ≤ 61) :
    q4 = 53 ∨ q4 = 59 ∨ q4 = 61 := by
  sorry

end OddPerfectNumber
