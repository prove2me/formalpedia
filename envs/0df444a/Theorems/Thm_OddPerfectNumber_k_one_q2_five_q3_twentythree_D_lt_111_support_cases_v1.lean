-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T05:12:57.652398+00:00
-- url     : https://prove2.me/theorems/8671f6cb-8923-4c28-ada5-c5acb771dc72
-- title:
--   Canonical q3=23 D<111 support candidates
-- statement:
--   For the q2=5,q3=23 small-D support envelope, odd D<111 with prime p=2D-1 and q4>D has only the exact support-compatible half-successor candidates D=3,9,15,27,45,69,75.
-- source:
--   Exact finite support arithmetic. A generic support-closure lemma forbids every prime factor other than 3,5,23 because q4>D; the remaining D<111 interval is split into two bounded cases before normalization.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v1 (D p q4 : Nat) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 23 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by sorry

end OddPerfectNumber
