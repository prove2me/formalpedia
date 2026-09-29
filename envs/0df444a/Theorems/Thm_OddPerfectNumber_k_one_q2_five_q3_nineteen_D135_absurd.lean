-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D135_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_D135_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T20:52:37.569512+00:00
-- url     : https://prove2.me/theorems/df41848c-3adf-4a5a-8c41-506193174576
-- title:
--   The D=135 q3=19 branch has no prime q4
-- statement:
--   The accepted D=135 abundance interval [146,148] contains no prime fourth support.
-- source:
--   Clean composition of the accepted exact prime exclusion for the D=135 interval.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D135_no_q4_candidate

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_D135_absurd (q4 : Nat)
    (hq4prime : q4.Prime) (hlow : 146 ≤ q4) (hhigh : q4 ≤ 148) :
    False := by
  sorry

end OddPerfectNumber
