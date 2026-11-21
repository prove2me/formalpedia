-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkedHorizonIntegrand_setIntegral_count_eq_integral_add
-- name    : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.setIntegral_count_eq_integral_add
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:38:28.572101+00:00
-- url     : https://prove2.me/theorems/ca23df04-9a07-4423-a38a-7e50b538b2c5
-- title:
--   setIntegral count eq integral add
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.setIntegral_count_eq_integral_add` is extracted from `LevyStochCalc.Poisson.CellIntegrand`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CellIntegrand_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A continuous adapted factor in a marked integrand

A bounded continuous adapted process, cut to a window of finite mark measure, multiplies a
predictable marked integrand carried by that window into another one: the product is predictable
(`Probability/PredictableContinuous.lean`), vanishes off the horizon and has finite energy. Since
the product is predictable it is pathwise, so on the window the integral of the product against
the random measure is its compensated integral plus its integral against the reference intensity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Cut

namespace MarkedHorizonIntegrand

variable {T : ℝ}

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.setIntegral_count_eq_integral_add (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (G : MarkedHorizonIntegrand P ν ℱ T) {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {C : ℝ} (hC0 : 0 ≤ C) (hXb : ∀ s ω, |X s ω| ≤ C) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun) (hT : 0 < T)
    {τ : ℝ} (hτT : τ ≤ T) :
    ∀ᵐ ω ∂P, (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A, X q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω))
      = (G.cutMul hXc hXa hC0 hXb hA hAν hGpred τ).integral N hℱ ω
        + ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
            X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν) := by sorry
