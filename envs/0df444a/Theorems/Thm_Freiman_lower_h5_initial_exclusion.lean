-- Prove2me | Theorems.Thm_Freiman_lower_h5_initial_exclusion
-- name    : Freiman.lower_h5_initial_exclusion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:53:06.734659+00:00
-- url     : https://prove2.me/theorems/06e05adf-8552-4db2-a59b-a823494dccff
-- title:
--   Freiman p97: initial exclusion
-- statement:
--   Combine the actual fixed, six-entry and marked-bridge root cases.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_initial_exclusion (t : ℝ) (p : LowerPair) (hp : lowerInitialRoot t p) : ¬(lowerMixed p ∧ lowerL p) := by
  sorry
