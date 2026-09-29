-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_D_lt_45_candidates
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_D_lt_45_candidates
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-14T18:10:56.211703+00:00
-- url     : https://prove2.me/theorems/fa6c3194-a7e1-4b58-befc-4e4b314bacb7
-- title:
--   The q3=13 D<45 half-successor candidates
-- statement:
--   If D<45, p=2D-1 is prime, and the fourth support prime q4>13 divides D, then the exact finite candidates are (19,37,19), (31,61,31), or (37,73,37).
-- source:
--   Finite exact arithmetic only: bound D and q4, enumerate the natural-number interval, and eliminate non-prime half-successors and unsupported q4 values by norm_num.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_D_lt_45_candidates (D p q4 : Nat)
    (hD : D < 45) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 13 < q4) (hq4dvd : q4 ∣ D) :
    (D = 19 ∧ p = 37 ∧ q4 = 19) ∨
      (D = 31 ∧ p = 61 ∧ q4 = 31) ∨
      (D = 37 ∧ p = 73 ∧ q4 = 37) := by
  sorry

end OddPerfectNumber
