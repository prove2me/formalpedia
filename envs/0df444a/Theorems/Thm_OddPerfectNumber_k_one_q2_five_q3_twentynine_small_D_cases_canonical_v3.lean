-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_canonical_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T08:46:49.89907+00:00
-- url     : https://prove2.me/theorems/e63e5d39-fcff-46e0-92a2-d81151c6b162
-- title:
--   Canonical q3=29 small-D support cases v3
-- statement:
--   The canonical q3=29 small-D support enumeration, with explicit prime-survivor dispatch and no D<q4 premise.
-- source:
--   Materially changed finite proof: derive the exact prime/odd D disjunction before applying support contradictions.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_small_D_cases_canonical_v3 (D p q4 : Nat) (hDgt : 15 < D) (hDlt : D < 75) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) : D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  sorry

end OddPerfectNumber
