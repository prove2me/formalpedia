-- Prove2me | Theorems.Thm_Freiman_lower_h5_early_priority
-- name    : Freiman.lower_h5_early_priority
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:55:15.79014+00:00
-- url     : https://prove2.me/theorems/3d3e9efb-5d50-4b06-962f-2f346c29a4fd
-- title:
--   Freiman p97: early priority
-- statement:
--   Connectedness of the already certified earlier chain, its actual C32 lower anchor, endpoint order, and exclusion of every offered chain member force the target above C22. This uses an earlier chain only.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_early_priority (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true)
    (p : LowerPair) (t : ℝ) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (hg : lowerEarlyGeometry p)
    (ha : lowerLocalLower p ([3],[2]) ≤ lowerH5ParentLower p)
    (hp : ∀ l ∈ lowerEarlyList p, t ∉ lowerCover (lowerChild p l)) :
    lowerH5LocalUpper p ([2],[2]) < lowerLocalCoordinate p t := by
  sorry
