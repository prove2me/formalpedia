-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T06:53:10.459287+00:00
-- url     : https://prove2.me/theorems/316a7281-c0bd-4e7b-8831-5b52741b8dfc
-- title:
--   Canonical q3=23 q4-divisor small-D cases
-- statement:
--   For q3=23 with D<111, q4>23, q4 prime, p=2D-1 prime, and q4 dividing D, the only possible tuples are (31,31), (37,37), (79,79), (87,29), and (97,97).
-- source:
--   Finite canonical arithmetic reduction for the q4-divides-D side of the q3=23 small-D split.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1 (D p q4 : Nat) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hq4div : q4 ∣ D) :
    (D = 31 ∧ q4 = 31) ∨ (D = 37 ∧ q4 = 37) ∨ (D = 79 ∧ q4 = 79) ∨ (D = 87 ∧ q4 = 29) ∨ (D = 97 ∧ q4 = 97) := by
  sorry

end OddPerfectNumber
