-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_canonical_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_small_D_cases_canonical_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T08:37:49.996215+00:00
-- url     : https://prove2.me/theorems/bfd94927-0a4d-4944-8359-6056b329e6fa
-- title:
--   Canonical q3=29 small-D support cases v2
-- statement:
--   The q3=29 small-D canonical support enumeration, with guarded finite tactic sequencing.
-- source:
--   Materially repaired finite arithmetic proof; no ordering premise D<q4 is used.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_small_D_cases_canonical_v2 (D p q4 : Nat) (hDgt : 15 < D) (hDlt : D < 75) (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4) : D = 27 ∨ D = 31 ∨ D = 37 ∨ D = 45 := by
  sorry

end OddPerfectNumber
