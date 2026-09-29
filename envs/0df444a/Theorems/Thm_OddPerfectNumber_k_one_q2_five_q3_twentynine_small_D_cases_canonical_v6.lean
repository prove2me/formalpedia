-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_canonical_v6
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v6
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T09:08:50.891235+00:00
-- url     : https://prove2.me/theorems/beafd791-9ffc-4975-8ecf-21d3cf121171
-- title:
--   Canonical q3=29 small-D support cases v6
-- statement:
--   The canonical q3=29 small-D support enumeration with separate hypothesis normalization in four bounded intervals.
-- source:
--   Finite canonical support reduction with separate hDodd and hp normalization stages to avoid closed-goal sequencing failures.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_small_D_cases_canonical_v6 (D p q4 : Nat) (hDgt : 15 < D) (hDlt : D < 75) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) : D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  sorry

end OddPerfectNumber
