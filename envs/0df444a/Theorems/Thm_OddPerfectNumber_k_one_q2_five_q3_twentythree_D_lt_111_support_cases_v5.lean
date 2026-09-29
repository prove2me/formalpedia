-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T05:25:10.01045+00:00
-- url     : https://prove2.me/theorems/a0a18f68-767e-4772-8f88-594dc094e8c0
-- title:
--   Canonical q3=23 D<111 support candidates (v5)
-- statement:
--   Under the canonical q3=23 small-D support and half-successor conditions, the only possible deficient factors are 3, 9, 15, 27, 45, 69, and 75.
-- source:
--   The q4 support arm substitutes the support equality before applying Nat.le_of_dvd. After each interval_cases call, all_goals stages hypothesis normalization and then the exact finite disjunction normalization.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5 (D p q4 : Nat) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 23 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by sorry

end OddPerfectNumber
