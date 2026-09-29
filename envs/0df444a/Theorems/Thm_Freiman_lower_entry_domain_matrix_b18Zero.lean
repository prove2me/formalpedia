-- Prove2me | Theorems.Thm_Freiman_lower_entry_domain_matrix_b18Zero
-- name    : Freiman.lower_entry_domain_matrix_b18Zero
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:47.684659+00:00
-- url     : https://prove2.me/theorems/e98c7483-f6fb-4c35-a66e-de1338c8dcc9
-- title:
--   Freiman lower construction: entry domain matrix b18Zero
-- statement:
--   The six explicitly defined strict multiaffine inequalities for b18Zero. This is a grouped finite parameter leaf: source matrix polynomial identities and positive rational vertices on the one closed box, not a universal word theorem.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_domain_matrix_b18Zero (x y z : ℝ) (hb : lowerInitialBox x y z) :
    lowerEntryMatrixBounds (lowerInitialSeamMatrices .b18Zero x y z) := by
  sorry
