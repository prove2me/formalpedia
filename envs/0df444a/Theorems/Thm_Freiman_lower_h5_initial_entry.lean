-- Prove2me | Theorems.Thm_Freiman_lower_h5_initial_entry
-- name    : Freiman.lower_h5_initial_entry
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:52:51.44078+00:00
-- url     : https://prove2.me/theorems/1f05d277-784d-492a-a457-31cf3debeb79
-- title:
--   Freiman p97: initial entry
-- statement:
--   For the six actual H-entry labels, only10 is mixed; the printed rational width bound forces it to reflect and its new wider side ends3. Uses the previously bound H-entry domain and suffix classes.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_initial_entry (hctx : ∀ (f : LowerInitialFamily) (n k p : ℕ), ∃ c : LowerEntryClass,
    lowerEntryContext c (lowerNormalize (lowerFamilyPair f n k p)) ∧
    lowerFamilyH f n k p = lowerEntryH c (lowerNormalize (lowerFamilyPair f n k p)))
    (hdom : ∀ (f : LowerInitialFamily) (n k p : ℕ), lowerEntryDomain (lowerNormalize (lowerFamilyPair f n k p)))
    (f : LowerInitialFamily) (n k p : ℕ) (l : LowerLabel) (hl : l ∈ lowerEntryLabels) :
    ¬(lowerMixed (lowerChild (lowerFamilyPair f n k p) l) ∧ lowerL (lowerChild (lowerFamilyPair f n k p) l)) := by
  sorry
