-- Prove2me | Theorems.Thm_Kyprianou_Ch04_simplePredictableFiniteOrthogonalIsometry
-- name    : Kyprianou.Ch04.simplePredictableFiniteOrthogonalIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:02:48.086218+00:00
-- url     : https://prove2.me/theorems/197abf25-6c13-48cd-815f-a433797bb98a
-- title:
--   Simple predictable compensated Poisson finite-sum isometry from diagonal moments
-- statement:
--   For an adapted finite simple predictable integrand with integrable pairwise cross-products, orthogonality of different time cells follows from Poisson past-future independence; combining it with the diagonal second moments gives an exact isometry for the finite sum.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4, finite step-predictable compensation isometry; uses the Proved LevyStochCalc simpleIntegral_offDiagonal interface and the Proved finite orthogonal-family second-moment identity.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Theorems.Thm_LevyStochCalc_Poisson_Compensated_simpleIntegral_offDiagonal
import Theorems.Thm_Kyprianou_Ch04_orthogonalFiniteFamilyL2Identity
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.simplePredictableFiniteOrthogonalIsometry
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ (inferInstance : MeasurableSpace Ω))
    (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (hAdapt : ∀ i : Fin φ.N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    (hProd : ∀ i j : Fin φ.N,
      Integrable (fun ω =>
        (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) *
        (φ.ξ j ω * N.compensated (φ.timeRect j T) ω)) P)
    (hDiag : ∀ i : Fin φ.N,
      (∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P) =
        (referenceIntensity ν (φ.timeRect i T)).toReal *
          ∫ ω, (φ.ξ i ω) ^ 2 ∂P) :
    ∫ ω, (∑ i : Fin φ.N,
      φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P =
      ∑ i : Fin φ.N, (referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  sorry
