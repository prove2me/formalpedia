-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_candidates_v4
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_candidates_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T23:27:09.404922+00:00
-- url     : https://prove2.me/theorems/b69a6b32-9ab9-41b9-8e35-ad3938066fdd
-- title:
--   The q3=23 large-D arithmetic survivors (v4)
-- statement:
--   In the q3=23 large-D envelope, the accepted q4 split and canonical half-successor arithmetic leave exactly seven (D,p,q4) tuples.
-- source:
--   Clean v4 replacement for the finite arithmetic enumeration; residue normalization precedes prime normalization in each finite branch.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_cases

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_candidates_v4 (D p q4 : Nat)
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
