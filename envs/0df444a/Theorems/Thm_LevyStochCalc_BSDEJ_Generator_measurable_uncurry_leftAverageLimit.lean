-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Generator_measurable_uncurry_leftAverageLimit
-- name    : LevyStochCalc.BSDEJ.Generator.measurable_uncurry_leftAverageLimit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T09:49:03.619321+00:00
-- url     : https://prove2.me/theorems/05f9a423-a991-4be0-a463-2e3655dddd79
-- title:
--   measurable uncurry leftAverageLimit
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Generator.measurable_uncurry_leftAverageLimit` is extracted from `LevyStochCalc.BSDEJ.DriftModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A progressive modification of a drift progressive for the right-continuous filtration

A real process that is progressively measurable for the right-continuous filtration `ℱ₊` has a
modification, equal to it almost everywhere on `Ω × [0, T]`, that is progressively measurable for
`ℱ` itself. The modification is the pointwise `limsup` of the moving averages of the process over
the windows `[s - 2c, s - c]` lying strictly to the left of `s`: each such average is
`ℱ`-progressive because it reads the process only before `s`, and Lebesgue's differentiation
theorem identifies the limit with the process at almost every time.
-/

open MeasureTheory Filter Metric
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### Moving averages over a window strictly to the left -/

/-! ### Lebesgue differentiation along the left windows -/

/-! ### The modification -/

theorem _root_.LevyStochCalc.BSDEJ.Generator.measurable_uncurry_leftAverageLimit (hbm : Measurable (Function.uncurry b)) (T : ℝ) :
    Measurable (Function.uncurry (leftAverageLimit b T)) := by sorry
