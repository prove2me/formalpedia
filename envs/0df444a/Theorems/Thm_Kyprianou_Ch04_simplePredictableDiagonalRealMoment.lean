-- Prove2me | Theorems.Thm_Kyprianou_Ch04_simplePredictableDiagonalRealMoment
-- name    : Kyprianou.Ch04.simplePredictableDiagonalRealMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:14:39.144835+00:00
-- url     : https://prove2.me/theorems/7054b5fd-617b-400f-83ea-f6aff181e175
-- title:
--   Real diagonal second moment for a simple predictable Poisson integral
-- statement:
--   For one adapted finite-variance predictable Poisson time cell, the expected squared compensated stochastic integral equals the intensity multiplied by the expected square of its predictable weight.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4; conversion of the Proved LevyStochCalc extended-nonnegative diagonal isometry to the corresponding real second-moment identity.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Theorems.Thm_LevyStochCalc_Poisson_Compensated_simpleIntegral_diagonal
import Theorems.Thm_Kyprianou_Ch04_squareL2IntegralEqNnnorm
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.simplePredictableDiagonalRealMoment
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ (inferInstance : MeasurableSpace Ω))
    (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (hPart : 0 ≤ φ.partition i.castSucc)
    (hAdapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    (hInt : Integrable
      (fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2) P)
    (hWeightInt : Integrable (fun ω => (φ.ξ i ω) ^ 2) P) :
    (∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P) =
      (referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  sorry
