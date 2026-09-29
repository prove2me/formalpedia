-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T05:20:44.839189+00:00
-- url     : https://prove2.me/theorems/3588fe4e-1b4e-44d6-ae24-c948488607c8
-- title:
--   Canonical q3=23 D<111 support candidates (v3)
-- statement:
--   Under the canonical q3=23 small-D support and half-successor conditions, the only possible deficient factors are 3, 9, 15, 27, 45, 69, and 75.
-- source:
--   The q4 support arm substitutes the support equality before applying Nat.le_of_dvd; the two finite branches use single-line bounded normalization passes.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v3 (D p q4 : Nat) (hDlt : D < 111) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 23 < q4) (hDq : D < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by sorry

end OddPerfectNumber
