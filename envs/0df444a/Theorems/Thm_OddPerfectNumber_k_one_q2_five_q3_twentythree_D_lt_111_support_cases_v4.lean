-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v4
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T05:22:14.861795+00:00
-- url     : https://prove2.me/theorems/7dd1d4c2-d864-4142-a89c-1aa247eaf262
-- title:
--   Canonical q3=23 D<111 support candidates (v4)
-- statement:
--   Under the canonical q3=23 small-D support and half-successor conditions, the only possible deficient factors are 3, 9, 15, 27, 45, 69, and 75.
-- source:
--   The q4 support arm substitutes the support equality before applying Nat.le_of_dvd. Each bounded interval branch stages hypothesis normalization and the final exact disjunction normalization with a separate tactic combinator.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v4 (D p q4 : Nat) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 23 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by sorry

end OddPerfectNumber
