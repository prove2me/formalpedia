-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_candidates
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_candidates
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T18:22:57.060868+00:00
-- url     : https://prove2.me/theorems/4882a703-b45c-4afe-8bb9-bf7d4630db3a
-- title:
--   The q3=13 middle-D half-successor candidates
-- statement:
--   In the canonical q3=13 middle envelope 45≤D<214 with q4≤89, p=2D−1 prime, p≡1 mod 4, and q4>13 prime dividing D, the exact candidate list is the thirteen displayed triples.
-- source:
--   Finite exact arithmetic enumeration with no abundance approximation: derive 0<D from p.Prime and p=2D−1, obtain q4≤D from q4∣D, substitute p, and use bounded interval_cases with staged norm_num.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_middle_D_candidates (D p q4 : Nat)
    (hDlow : 45 ≤ D) (hDhigh : D < 214)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 13 < q4) (hq4le : q4 ≤ 89)
    (hq4dvd : q4 ∣ D) :
    (D = 51 ∧ p = 101 ∧ q4 = 17) ∨
      (D = 57 ∧ p = 113 ∧ q4 = 19) ∨
      (D = 69 ∧ p = 137 ∧ q4 = 23) ∨
      (D = 79 ∧ p = 157 ∧ q4 = 79) ∨
      (D = 87 ∧ p = 173 ∧ q4 = 29) ∨
      (D = 115 ∧ p = 229 ∧ q4 = 23) ∨
      (D = 129 ∧ p = 257 ∧ q4 = 43) ∨
      (D = 141 ∧ p = 281 ∧ q4 = 47) ∨
      (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
      (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
      (D = 187 ∧ p = 373 ∧ q4 = 17) ∨
      (D = 201 ∧ p = 401 ∧ q4 = 67) ∨
      (D = 205 ∧ p = 409 ∧ q4 = 41) := by
  sorry

end OddPerfectNumber
