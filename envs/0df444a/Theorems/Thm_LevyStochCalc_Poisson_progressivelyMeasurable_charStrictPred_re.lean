-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_progressivelyMeasurable_charStrictPred_re
-- name    : LevyStochCalc.Poisson.progressivelyMeasurable_charStrictPred_re
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:08:48.162409+00:00
-- url     : https://prove2.me/theorems/40388128-622d-4bc2-96bb-76a3d18831a3
-- title:
--   progressivelyMeasurable charStrictPred re
-- statement:
--   The source theorem `LevyStochCalc.Poisson.progressivelyMeasurable_charStrictPred_re` is extracted from `LevyStochCalc.Poisson.CharacterStrictProcess`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F002

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

end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}

variable (hℱ : IsPoissonFiltration N ℱ) (hBm : ∀ j, MeasurableSet (Bfam j))
  (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)

include hℱ hBm hA hAν in

theorem _root_.LevyStochCalc.Poisson.progressivelyMeasurable_charStrictPred_re (T : ℝ) (e₀ : E) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (charStrictPred N w Bfam A T e₀ s ω).re := by sorry
