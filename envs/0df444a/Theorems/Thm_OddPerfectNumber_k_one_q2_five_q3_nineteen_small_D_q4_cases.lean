-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_q4_cases
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_q4_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T19:03:35.048424+00:00
-- url     : https://prove2.me/theorems/2ce76087-68b8-4fe4-b202-866c6b46ecbe
-- title:
--   The q3=19 small-D fourth-prime candidates
-- statement:
--   The accepted prime interval certificates reduce the D=57 or D=75 q3=19 small-D envelope to the five exact tuples q4=587,593,599,601,263.
-- source:
--   Pure composition of the accepted D=57 four-way prime interval and D=75 unique-prime interval certificates.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_q4_candidates
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_q4_candidate

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_q4_cases (D q4 : Nat)
    (hq4prime : q4.Prime)
    (hDq4range :
      (D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨
      (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264)) :
    (D = 57 ∧ q4 = 587) ∨
      (D = 57 ∧ q4 = 593) ∨
      (D = 57 ∧ q4 = 599) ∨
      (D = 57 ∧ q4 = 601) ∨
      (D = 75 ∧ q4 = 263) := by
  sorry

end OddPerfectNumber
