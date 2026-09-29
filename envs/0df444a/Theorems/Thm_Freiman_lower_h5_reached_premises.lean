-- Prove2me | Theorems.Thm_Freiman_lower_h5_reached_premises
-- name    : Freiman.lower_h5_reached_premises
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:53:36.672677+00:00
-- url     : https://prove2.me/theorems/9aa7a557-6691-4ebd-866a-1a31b5d2b1f2
-- title:
--   Freiman p97: reached premises
-- statement:
--   Derive rectangle membership and the exact ancestor/current premises at the immediate earlier normalized pair. Uses actual goodness, normalized widths and positive pullback semantics; no future state is assumed.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_reached_premises (hg : LowerHistoryGoodnessLaw) (hpull : LowerHistoryPullLaw) (hwidth : LowerHistoryWidthLaw)
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) (c : LowerH5Case) (hshape : lowerH5CaseShape c)
    (hc : lowerH5Immediate h n c) : lowerH5ReachedPremises h n c := by
  sorry
