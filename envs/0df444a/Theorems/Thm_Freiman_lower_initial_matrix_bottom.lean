-- Prove2me | Theorems.Thm_Freiman_lower_initial_matrix_bottom
-- name    : Freiman.lower_initial_matrix_bottom
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:58.172341+00:00
-- url     : https://prove2.me/theorems/31191a4c-6b87-41a0-bcea-2c9ee618451b
-- title:
--   Freiman lower construction: initial matrix bottom
-- statement:
--   The lower row of the actual word matrix is exactly the existing lowerCD recurrence, so no new denominator ratio replaces the old one.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_initial_matrix_bottom (w : List ℕ+) : (lowerInitialWordMatrix w).c = ((lowerCD w).1:ℝ) ∧ (lowerInitialWordMatrix w).d = ((lowerCD w).2:ℝ) := by
  sorry
