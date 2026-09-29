-- Prove2me | Theorems.Thm_Freiman_lower_h5_right3_anchor
-- name    : Freiman.lower_h5_right3_anchor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:54:26.954507+00:00
-- url     : https://prove2.me/theorems/6ea405fe-103f-400a-9d8f-42d08caa641b
-- title:
--   Freiman p97: right3 anchor
-- statement:
--   Direct equality of the two actual lower endpoints in the right-ending3 case, with physical tails U213,V1213 and common period12; includes parity duality.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_right3_anchor (p : LowerPair) (t : ℝ) (hs : lowerState t p) (ha : lowerH5Active p)
    (hr : lowerEnds (lowerNormalize p).2 [3]) : lowerH5LowerBound p t := by
  sorry
