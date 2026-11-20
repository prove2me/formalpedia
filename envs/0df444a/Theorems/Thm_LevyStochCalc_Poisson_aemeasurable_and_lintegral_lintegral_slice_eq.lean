-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_aemeasurable_and_lintegral_lintegral_slice_eq
-- name    : LevyStochCalc.Poisson.aemeasurable_and_lintegral_lintegral_slice_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T12:47:46.270329+00:00
-- url     : https://prove2.me/theorems/f2b5e6ea-3534-4562-a607-f7f2ba053f31
-- title:
--   aemeasurable and lintegral lintegral slice eq
-- statement:
--   The source theorem `LevyStochCalc.Poisson.aemeasurable_and_lintegral_lintegral_slice_eq` is extracted from `LevyStochCalc.Poisson.Compensator`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Definitions.Def_LevyStochCalc_Poisson_FiniteActivity_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictable_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The reference intensity as compensator on a finite-activity window

On a predictable rectangle the count of the Poisson random measure is independent of the past
event carried by the rectangle, so its mean factorises as the probability of that event times
the intensity of the time–mark part. The sets on which the two mean occupations agree form a
Dynkin system — complements by subtracting from the finite occupation of the window, countable
disjoint unions by monotone convergence — so they agree on every predictable set.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Rectangle

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Rectangle

section Window

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Poisson.aemeasurable_and_lintegral_lintegral_slice_eq (hℱ : IsPoissonFiltration N ℱ)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    {Ψ : Ω × ℝ × E → ℝ≥0∞}
    (hΨ : Measurable[Probability.markedPredictableSigma ℱ ν] Ψ) :
    AEMeasurable (fun ω => ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(N.N ω)) P
      ∧ Measurable (fun ω =>
          ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(referenceIntensity ν))
      ∧ ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(N.N ω) ∂P
          = ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(referenceIntensity ν) ∂P := by sorry
