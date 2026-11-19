-- Prove2me | Theorems.Thm_LevyStochCalc_Analysis_eventually_jumpSum_leftPt
-- name    : LevyStochCalc.Analysis.eventually_jumpSum_leftPt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:17:05.856805+00:00
-- url     : https://prove2.me/theorems/2bdf99a4-c5dc-4516-b92a-0a92af4f09e4
-- title:
--   eventually jumpSum leftPt
-- statement:
--   The source theorem `LevyStochCalc.Analysis.eventually_jumpSum_leftPt` is extracted from `LevyStochCalc.Analysis.FiniteJumpSum`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_FiniteJumpSum_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Sums of finitely many jumps along a dyadic grid

A finite set of points of `ℝ × E` with weights defines a step function of the time,
`jumpSum S c s`, the sum of the weights of the points with time in `(0, s]`, and its strict-past
version `jumpSumStrict S c s`. Along the dyadic grid of `[0, t]` the frozen values
`jumpSum S c (leftPt t n s)` are eventually the strict-past value, and the sums of the increments
over the cells weighted by a continuous function at the right endpoints converge to the sum of
the weights times the function at the points. A finite sum of Dirac masses integrates a function
over a time window to such a jump sum.
-/

open Filter MeasureTheory
open scoped Topology BigOperators

namespace LevyStochCalc.Analysis

variable {E : Type*}

section Sums

theorem _root_.LevyStochCalc.Analysis.eventually_jumpSum_leftPt (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) {t : ℝ} (ht : 0 < t)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, jumpSum S c (leftPt t n s) = jumpSumStrict S c s := by sorry
