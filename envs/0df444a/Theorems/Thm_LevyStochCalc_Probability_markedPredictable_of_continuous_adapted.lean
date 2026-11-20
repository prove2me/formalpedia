-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_markedPredictable_of_continuous_adapted
-- name    : LevyStochCalc.Probability.markedPredictable_of_continuous_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:59:06.097702+00:00
-- url     : https://prove2.me/theorems/55450a8f-59e7-44dd-8c8a-298d13030124
-- title:
--   markedPredictable of continuous adapted
-- statement:
--   The source theorem `LevyStochCalc.Probability.markedPredictable_of_continuous_adapted` is extracted from `LevyStochCalc.Probability.PredictableContinuous`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_PredictableContinuous_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A continuous adapted process, cut to a window, is marked predictable

Freezing a continuous adapted process at the left endpoints of the level-`n` dyadic slabs gives a
step process whose coefficients are known at those endpoints, hence a marked predictable process
for every level. The endpoints increase to the time from strictly below, so on a window of finite
mark measure the frozen processes converge pointwise to the process itself, which is therefore
marked predictable there.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Poisson (dyadicLeft dyadicLeft_lt sub_le_dyadicLeft)

theorem _root_.LevyStochCalc.Probability.markedPredictable_of_continuous_adapted {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hX : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    MarkedPredictable ℱ ν fun ω s e =>
      (Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ : ℝ × E => X s ω) (s, e) := by sorry
