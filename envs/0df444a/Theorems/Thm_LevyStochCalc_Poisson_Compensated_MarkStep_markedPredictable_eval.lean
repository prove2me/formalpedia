-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkStep_markedPredictable_eval
-- name    : LevyStochCalc.Poisson.Compensated.MarkStep.markedPredictable_eval
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T12:42:26.823476+00:00
-- url     : https://prove2.me/theorems/87faca10-b40f-4afb-9b2b-3394f3914ad5
-- title:
--   markedPredictable eval
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.markedPredictable_eval` is extracted from `LevyStochCalc.Poisson.MarkStepPathwise`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepPathwise_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-step approximants are pathwise and predictable

The approximants the compensated integral is built from are finite combinations of indicators of
time–mark rectangles with coefficients known at the left endpoint of their piece. Their integral
against any measure finite on those rectangles is the matching finite combination, so over the
whole horizon the approximant's compensated integral is the difference of its integrals against
the random measure and against the reference intensity. Adaptedness of the coefficients makes the
approximant predictable, which is what the compensator identity asks for.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P] {g : TimeGrid}

namespace MarkStep

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkStep.markedPredictable_eval (G : MarkStep Ω E ν g)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hG : G.Adapted ℱ) :
    Probability.MarkedPredictable ℱ ν fun ω s e => G.eval s e ω := by sorry
