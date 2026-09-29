-- Prove2me | Theorems.Thm_Freiman_lower_h5_priority_cover_identity
-- name    : Freiman.lower_h5_priority_cover_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:53:45.065117+00:00
-- url     : https://prove2.me/theorems/b0d04c4f-e152-4845-8ce6-1db1c36ae957
-- title:
--   Freiman p97: priority cover identity
-- statement:
--   Use forced strict reflection twice to identify P/20 with Z/22 in the same incoming normalization and local scalar coordinate. Equality of full widths is not substituted for this strict statement.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_priority_cover_identity (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p →
    let q := lowerNormalize p
    lowerWidth (q.1++[2]) < lowerWidth q.2 ∧ lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
    lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧ lowerWidth (q.2++[1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (n m : ℕ) (hh : lowerHistory t h n) (he : LowerH5PriorityEvent t h n m) :
    lowerLocalLower (h n) ([2],[]) = lowerLocalLower (h m) ([2],[2]) ∧
    lowerH5LocalUpper (h n) ([2],[]) = lowerH5LocalUpper (h m) ([2],[2]) ∧
    lowerLocalCoordinate (h n) t = lowerLocalCoordinate (h m) t := by
  sorry
