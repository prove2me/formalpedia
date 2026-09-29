-- Prove2me | Theorems.Thm_Freiman_lower_h5_marked_priority
-- name    : Freiman.lower_h5_marked_priority
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:54:24.284215+00:00
-- url     : https://prove2.me/theorems/a1d2fe4f-8fe3-4a4f-abd2-c6ad99a4c7a5
-- title:
--   Freiman p97: marked priority
-- statement:
--   The earlier row2 lower bound and actual C22 priority exclusion place the carried scalar strictly above that cover, including odd common parity.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_marked_priority (p : LowerPair) (t : ℝ)
    (hl : lowerLocalLower p ([2],[2]) ≤ lowerLocalCoordinate p t)
    (hp : t ∉ lowerCover (lowerChild p ([2],[2]))) : lowerH5LocalUpper p ([2],[2]) < lowerLocalCoordinate p t := by
  sorry
