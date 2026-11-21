-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_MarkedHorizonIntegrand_integral_mulLeft
-- name    : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mulLeft
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:43:43.870299+00:00
-- url     : https://prove2.me/theorems/a816ad86-869a-493d-8a4c-af1f9f161be2
-- title:
--   integral mulLeft
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mulLeft` is extracted from `LevyStochCalc.Poisson.CompensatedPullOut`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside a compensated integral

A bounded weight measurable at time `a` times the compensated integral of a marked integrand
vanishing up to `a` is the compensated integral of the weighted integrand. The identity is proved
in `L²`: the squared distance between the two sides expands, through the Itô–Lévy isometry and
the quadratic-variation martingale started at `a`, into a combination of weighted compensators
that cancels.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Vanishing

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤)

end Vanishing

section Weighted

namespace MarkedHorizonIntegrand

variable {T : ℝ}

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

theorem _root_.LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mulLeft (hT : 0 < T) (G : MarkedHorizonIntegrand P ν ℱ T) {a : ℝ} (ha : 0 ≤ a)
    (haT : a ≤ T) (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {V : Ω → ℝ}
    (hVm : StronglyMeasurable[ℱ a] V) {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) :
    (G.mulLeft hGa hVm hVb).integral N hℱ =ᵐ[P] fun ω => V ω * G.integral N hℱ ω := by sorry
