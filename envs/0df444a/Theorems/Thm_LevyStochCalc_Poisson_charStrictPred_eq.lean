-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_charStrictPred_eq
-- name    : LevyStochCalc.Poisson.charStrictPred_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:00:47.797718+00:00
-- url     : https://prove2.me/theorems/05dc4a4b-8437-4b4f-8bbe-6e0271eebd5c
-- title:
--   charStrictPred eq
-- statement:
--   The source theorem `LevyStochCalc.Poisson.charStrictPred_eq` is extracted from `LevyStochCalc.Poisson.CharacterStrictProcess`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F001

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

theorem _root_.LevyStochCalc.Poisson.charStrictPred_eq (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} {A : Set E} {b T : ℝ} (hT : 0 < T) (hbT : b < T)
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A) (s : ℝ) (ω : Ω) :
    charStrictPred N w Bfam A T e₀ s ω = charStrict N w Bfam s ω := by sorry
