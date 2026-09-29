-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_q4_cases_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_q4_cases_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T14:20:14.321084+00:00
-- url     : https://prove2.me/theorems/355ade71-0eab-4a43-8698-0e629904497a
-- title:
--   Canonical q3=29 D=27 fourth-prime cases
-- statement:
--   A prime q4 with 29<q4≤89 is one of the fourteen explicit primes in the D=27 q3=29 branch.
-- source:
--   Split 30≤q4≤89 into four narrow intervals and use exact primality evaluation for each numeral.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D27_q4_cases_v1 (q4 : Nat) (hq4prime : q4.Prime) (hq4gt : 29 < q4) (hq4le : q4 ≤ 89) : q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 ∨ q4 = 47 ∨ q4 = 53 ∨ q4 = 59 ∨ q4 = 61 ∨ q4 = 67 ∨ q4 = 71 ∨ q4 = 73 ∨ q4 = 79 ∨ q4 = 83 ∨ q4 = 89 := by
  sorry

end OddPerfectNumber
