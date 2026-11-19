-- Prove2me | Theorems.Thm_LevyStochCalc_Analysis_tendsto_leftPt
-- name    : LevyStochCalc.Analysis.tendsto_leftPt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:16:34.672502+00:00
-- url     : https://prove2.me/theorems/cab11f6f-32ac-4d73-9e12-a007ecba769c
-- title:
--   tendsto leftPt
-- statement:
--   The source theorem `LevyStochCalc.Analysis.tendsto_leftPt` is extracted from `LevyStochCalc.Analysis.DyadicGrid`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_DyadicGrid_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The dyadic partition of an interval

The dyadic partition of `[0, t]` of level `n`, its strict monotonicity, and the left endpoint
`leftPt t n s` of the cell containing a time `s ∈ (0, t]`, which tends to `s` from below.
-/

open Filter
open scoped Topology

namespace LevyStochCalc.Analysis

section Grid

theorem _root_.LevyStochCalc.Analysis.tendsto_leftPt {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => leftPt t n s) atTop (𝓝 s) := by sorry
