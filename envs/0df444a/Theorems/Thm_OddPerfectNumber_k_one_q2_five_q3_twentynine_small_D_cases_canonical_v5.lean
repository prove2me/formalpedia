-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_canonical_v5
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v5
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T09:06:42.181595+00:00
-- url     : https://prove2.me/theorems/736384b2-7e5b-4ea9-8f12-bb4fa736e9d4
-- title:
--   Canonical q3=29 small-D support cases v5
-- statement:
--   The canonical q3=29 small-D support enumeration with four small interval certificates and explicit unsupported-prime closure.
-- source:
--   The v5 source stages each bounded interval separately and closes unsupported-prime branches using the strict q4 lower bound.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_small_D_cases_canonical_v5 (D p q4 : Nat) (hDgt : 15 < D) (hDlt : D < 75) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) : D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  sorry

end OddPerfectNumber
