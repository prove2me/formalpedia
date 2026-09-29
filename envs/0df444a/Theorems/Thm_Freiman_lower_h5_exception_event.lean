-- Prove2me | Theorems.Thm_Freiman_lower_h5_exception_event
-- name    : Freiman.lower_h5_exception_event
-- status  : Disproved
-- author  : @tp
-- created : 2026-09-09T13:53:39.160424+00:00
-- url     : https://prove2.me/theorems/12adca3d-4b4f-4413-99cb-25790bfa6bdb
-- title:
--   Freiman p97: exception event
-- statement:
--   Translate exactly the three B2/H9/notH16 cases into the real selected20 predecessor, earlier depth m<n, and its stored early-chain/C22 priority rule.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_exception_event (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (c : LowerH5Case) (hshape : lowerH5CaseShape c) (hc : lowerH5Immediate h n c)
    (he : lowerH5Exceptional c) : ∃ m : ℕ, LowerH5PriorityEvent t h n m := by
  sorry
