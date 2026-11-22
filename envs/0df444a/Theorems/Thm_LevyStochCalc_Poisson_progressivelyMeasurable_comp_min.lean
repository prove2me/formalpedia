-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_progressivelyMeasurable_comp_min
-- name    : LevyStochCalc.Poisson.progressivelyMeasurable_comp_min
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:02:22.226561+00:00
-- url     : https://prove2.me/theorems/551a5e4a-84a9-46fe-bdb4-d5a74bd83004
-- title:
--   progressivelyMeasurable comp min
-- statement:
--   The source theorem `LevyStochCalc.Poisson.progressivelyMeasurable_comp_min` is extracted from `LevyStochCalc.Poisson.CharacterStrictProcess`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strict-past character as a progressively measurable process

The predictable representative of the strictly-past window sum, evaluated at a fixed mark of the
window and at the time clamped to the horizon, is a jointly measurable and progressively
measurable process. For a family carried strictly before the horizon it is exactly the exponent
of the strict-past character at every time, so the strict-past character is itself progressively
measurable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Evaluation

omit [IsProbabilityMeasure P] [SigmaFinite ν] in

theorem _root_.LevyStochCalc.Poisson.progressivelyMeasurable_comp_min {f : Ω → ℝ → ℝ}
    (h : Probability.ProgressivelyMeasurable ℱ f) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => f ω (min s T) := by sorry
