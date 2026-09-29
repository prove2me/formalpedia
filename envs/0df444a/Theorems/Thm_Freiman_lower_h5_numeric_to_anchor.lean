-- Prove2me | Theorems.Thm_Freiman_lower_h5_numeric_to_anchor
-- name    : Freiman.lower_h5_numeric_to_anchor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:53:12.031153+00:00
-- url     : https://prove2.me/theorems/d3992cf4-1476-412b-957e-f01977d10b32
-- title:
--   Freiman p97: numeric to anchor
-- statement:
--   Select the actual endpoint comparison from the overincluded weak-normalization cases, transfer its polynomial order through common parity, and use t in the current cover. The only possible numerical fallback is the specified exceptional predecessor.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_numeric_to_anchor (he : LowerHistoryEndpointLaw) (hg : LowerHistoryGreaterLaw)
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) (c : LowerH5Case) (hshape : lowerH5CaseShape c)
    (hc : lowerH5Immediate h n c) (hs : lowerH5ReachedPremises h n c)
    (hn : lowerH5Numeric c) : lowerH5LowerBound (h n) t ∨ lowerH5Exceptional c := by
  sorry
