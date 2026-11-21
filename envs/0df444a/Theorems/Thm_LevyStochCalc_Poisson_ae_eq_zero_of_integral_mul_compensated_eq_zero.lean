-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_ae_eq_zero_of_integral_mul_compensated_eq_zero
-- name    : LevyStochCalc.Poisson.ae_eq_zero_of_integral_mul_compensated_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:19:55.937955+00:00
-- url     : https://prove2.me/theorems/d3743889-e32c-4cb8-b00e-8a1752873a72
-- title:
--   ae eq zero of integral mul compensated eq zero
-- statement:
--   The source theorem `LevyStochCalc.Poisson.ae_eq_zero_of_integral_mul_compensated_eq_zero` is extracted from `LevyStochCalc.Poisson.PredictableRepresentation`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable representation property of a Poisson random measure

A square-integrable weight of mean zero, measurable at the horizon for a filtration below the
augmented natural filtration of the random measure and orthogonal to every compensated integral
over the horizon, is orthogonal to the character of every finite family of window sets
(`charPairing_eq_zero`), so it vanishes by the separation of the window family
(`ae_eq_zero_of_integral_char_window`). Fed into the orthogonal decomposition
`Compensated.exists_markedHorizonIntegrand_of_mean_zero`, this represents every square-integrable
weight of mean zero measurable at the horizon as a compensated integral of a horizon integrand.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Poisson.ae_eq_zero_of_integral_mul_compensated_eq_zero (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T)
    (hℱT : ℱ T ≤ Probability.aug (naturalFiltration N T) ‹MeasurableSpace Ω› P)
    {r : Ω → ℝ} (hr2 : MemLp r 2 P) (hrm : AEStronglyMeasurable[ℱ T] r P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0) :
    r =ᵐ[P] 0 := by sorry
