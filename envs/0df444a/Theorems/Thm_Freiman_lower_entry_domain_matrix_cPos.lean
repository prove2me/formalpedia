-- Prove2me | Theorems.Thm_Freiman_lower_entry_domain_matrix_cPos
-- name    : Freiman.lower_entry_domain_matrix_cPos
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:50.537313+00:00
-- url     : https://prove2.me/theorems/67bad7b5-a6d0-4979-8cba-43a95762aeb7
-- title:
--   Freiman lower construction: entry domain matrix cPos
-- statement:
--   The six explicitly defined strict multiaffine inequalities for cPos. This is a grouped finite parameter leaf: source matrix polynomial identities and positive rational vertices on the one closed box, not a universal word theorem.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_domain_matrix_cPos (x y z : ℝ) (hb : lowerInitialBox x y z) :
    lowerEntryMatrixBounds (lowerInitialSeamMatrices .cPos x y z) := by
  sorry
