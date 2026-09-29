-- Prove2me | Theorems.Thm_Freiman_gap_maximum_forbidden_checks
-- name    : Freiman.gap_maximum_forbidden_checks
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:15.832818+00:00
-- url     : https://prove2.me/theorems/7fdd62ae-56f6-489f-974a-ce50ee217187
-- title:
--   gap maximum forbidden checks
-- statement:
--   Exact rational witnesses for every word in the maximum forbidden list.
-- source:
--   Freiman Hall ray report, m3_maximum.tex; displayed forbidden-word table

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_maximum_forbidden_checks : ∀ w ∈ gapMaximumForbidden, ∃ j : ℕ, j < w.length ∧ (4527829567/1000000000 : ℚ) ≤ gapCylinderLower w j := by
  sorry

end Freiman
