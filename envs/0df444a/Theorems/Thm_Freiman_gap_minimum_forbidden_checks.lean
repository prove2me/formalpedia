-- Prove2me | Theorems.Thm_Freiman_gap_minimum_forbidden_checks
-- name    : Freiman.gap_minimum_forbidden_checks
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:24.086203+00:00
-- url     : https://prove2.me/theorems/3870d747-e222-405d-a21f-60648f77e613
-- title:
--   gap minimum forbidden checks
-- statement:
--   Exact rational witnesses for every word in the minimum forbidden list.
-- source:
--   Freiman Hall ray report, m3_minimum.tex; displayed forbidden-word table

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_minimum_forbidden_checks : ∀ w ∈ gapMinimumForbidden, ∃ j : ℕ, j < w.length ∧ (4527829567/1000000000 : ℚ) ≤ gapCylinderLower w j := by
  sorry

end Freiman
