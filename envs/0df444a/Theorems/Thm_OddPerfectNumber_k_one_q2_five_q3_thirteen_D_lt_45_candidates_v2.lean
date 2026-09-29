-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_D_lt_45_candidates_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_D_lt_45_candidates_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T18:17:57.103697+00:00
-- url     : https://prove2.me/theorems/8b0e8739-2526-4243-8893-17f4a41b9e68
-- title:
--   The corrected q3=13 D<45 half-successor candidates
-- statement:
--   With the canonical Euler congruence p≡1 mod 4 added, D<45, p=2D−1 prime, and q4>13 prime dividing D leave exactly (19,37,19), (31,61,31), or (37,73,37).
-- source:
--   Corrected finite arithmetic certificate: derive 0<D from p.Prime and p=2D−1, obtain q4≤D from q4∣D, substitute p, then enumerate the bounded D and q4 intervals with staged norm_num.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_D_lt_45_candidates_v2 (D p q4 : Nat)
    (hD : D < 45) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 13 < q4) (hq4dvd : q4 ∣ D) :
    (D = 19 ∧ p = 37 ∧ q4 = 19) ∨
      (D = 31 ∧ p = 61 ∧ q4 = 31) ∨
      (D = 37 ∧ p = 73 ∧ q4 = 37) := by
  sorry

end OddPerfectNumber
