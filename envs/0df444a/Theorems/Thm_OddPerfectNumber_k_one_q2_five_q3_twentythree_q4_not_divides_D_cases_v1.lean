-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_not_divides_D_cases_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_not_divides_D_cases_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T06:55:24.386746+00:00
-- url     : https://prove2.me/theorems/30e96d4d-37d8-43f9-b13b-8792e7f03c17
-- title:
--   Canonical q3=23 q4-nondivisor small-D cases
-- statement:
--   For q3=23 with D<111, q4>23, q4 prime, p=2D-1 prime, q4 not dividing D, and all prime divisors of D in the support, the possible D values are 3,9,15,27,45,69,75.
-- source:
--   Finite canonical arithmetic reduction for the q4-nondivisor side of the q3=23 small-D split.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_q4_not_divides_D_cases_v1 (D p q4 : Nat) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hq4notdiv : ¬ q4 ∣ D) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) :
    D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by
  sorry

end OddPerfectNumber
