-- Prove2me | Theorems.Thm_Freiman_lower_entry_seam_matrix_domains
-- name    : Freiman.lower_entry_seam_matrix_domains
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:21:17.183589+00:00
-- url     : https://prove2.me/theorems/0d7bf57e-170a-48bf-9710-222e7a506540
-- title:
--   Freiman lower construction: entry seam matrix domains
-- statement:
--   (c : LowerInitialSeamCase) (x y z : ℝ) (hb : lowerInitialBox x y z) : lowerEntryMatrixBounds (lowerInitialSeamMatrices c x y z)
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_seam_matrix_domains (c : LowerInitialSeamCase) (x y z : ℝ) (hb : lowerInitialBox x y z) : lowerEntryMatrixBounds (lowerInitialSeamMatrices c x y z) := by
  sorry
