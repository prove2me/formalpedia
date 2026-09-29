-- Prove2me | Theorems.Thm_Freiman_lower_entry_domain_matrix_aZero
-- name    : Freiman.lower_entry_domain_matrix_aZero
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:45.298754+00:00
-- url     : https://prove2.me/theorems/c7a18ecf-46d1-40f7-87af-decc52f63f8a
-- title:
--   Freiman lower construction: entry domain matrix aZero
-- statement:
--   The six explicitly defined strict multiaffine inequalities for aZero. This is a grouped finite parameter leaf: source matrix polynomial identities and positive rational vertices on the one closed box, not a universal word theorem.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_domain_matrix_aZero (x y z : ℝ) (hb : lowerInitialBox x y z) :
    lowerEntryMatrixBounds (lowerInitialSeamMatrices .aZero x y z) := by
  sorry
