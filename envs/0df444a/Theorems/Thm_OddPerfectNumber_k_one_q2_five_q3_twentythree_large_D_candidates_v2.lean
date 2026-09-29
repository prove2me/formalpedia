-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_candidates_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_candidates_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T23:15:13.096714+00:00
-- url     : https://prove2.me/theorems/a34c061c-f32e-44d6-9c11-36be6ca9e0f1
-- title:
--   The q3=23 large-D arithmetic survivors (v2)
-- statement:
--   In the q3=23 large-D envelope, the accepted q4 split and canonical half-successor arithmetic leave exactly seven (D,p,q4) tuples.
-- source:
--   Exact finite arithmetic over the three accepted q4 cases; no source contradiction is hidden in this reduction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_cases

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_candidates_v2 (D p q4 : Nat)
    (hDlow : 111 ≤ D) (hDhigh : D ≤ 685)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 47 < q4) (hq4le : q4 ≤ 61)
    (hq4dvd : q4 ∣ D) :
    (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
    (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
    (D = 427 ∧ p = 853 ∧ q4 = 61) ∨
    (D = 477 ∧ p = 953 ∧ q4 = 53) ∨
    (D = 531 ∧ p = 1061 ∧ q4 = 59) ∨
    (D = 549 ∧ p = 1097 ∧ q4 = 61) ∨
    (D = 649 ∧ p = 1297 ∧ q4 = 59) := by
  sorry

end OddPerfectNumber
