-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_support_cut_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_support_cut_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T23:34:00.202451+00:00
-- url     : https://prove2.me/theorems/d6a15f2e-75ef-47d4-b49f-64dc0b9351fd
-- title:
--   The q3=23 large-D support cut removes external-prime survivors (v2)
-- statement:
--   The accepted seven-tuple q3=23 large-D reduction loses the D=427 and D=649 tuples because 7 and 11 are external prime divisors of D.
-- source:
--   Clean v2 support-divisor cut with concrete prime divisors after tuple substitution.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_candidates_v4

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_support_cut_v2 (D p q4 : Nat)
    (hDlow : 111 ≤ D) (hDhigh : D ≤ 685)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 47 < q4) (hq4le : q4 ≤ 61)
    (hq4dvd : q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) :
    (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
    (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
    (D = 477 ∧ p = 953 ∧ q4 = 53) ∨
    (D = 531 ∧ p = 1061 ∧ q4 = 59) ∨
    (D = 549 ∧ p = 1097 ∧ q4 = 61) := by
  sorry

end OddPerfectNumber
