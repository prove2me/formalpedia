-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_integral_mul_setIntegral_count
-- name    : LevyStochCalc.Driver.integral_mul_setIntegral_count
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:01:18.858127+00:00
-- url     : https://prove2.me/theorems/d077fe24-8886-488a-b4e2-aee2b70a5949
-- title:
--   integral mul setIntegral count
-- statement:
--   The source theorem `LevyStochCalc.Driver.integral_mul_setIntegral_count` is extracted from `LevyStochCalc.Driver.CellPairing`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellPairing_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing the jump term of the product rule

A weight orthogonal to every compensated integral over the horizon does not see the compensated
half of a window integral against the random measure: pairing it, times a bounded weight
measurable before the window, with the integral of a continuous adapted factor against the
random measure leaves only the integral against the reference intensity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section JumpTerm

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ}

theorem _root_.LevyStochCalc.Driver.integral_mul_setIntegral_count (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G.integral N hℱ ω ∂P = 0)
    {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V)
    {Mv : ℝ} (hVb : ∀ ω, |V ω| ≤ Mv)
    (G : MarkedHorizonIntegrand P ν ℱ T) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun)
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {Cg : ℝ} (hGb : ∀ ω s e, |G.toFun ω s e| ≤ Cg)
    {X : ℝ → Ω → ℝ} (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t)) {C : ℝ} (hC0 : 0 ≤ C)
    (hXb : ∀ s ω, |X s ω| ≤ C) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {τ : ℝ} (hτT : τ ≤ T) :
    ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
        X q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) ∂P
      = ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
          X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by sorry
