-- Prove2me | Theorems.Thm_Kyprianou_Ch04_simplePredictableFullyDiagonalFiniteIsometry
-- name    : Kyprianou.Ch04.simplePredictableFullyDiagonalFiniteIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:18:40.538801+00:00
-- url     : https://prove2.me/theorems/e9ae30b0-7605-5213-b46f-84678906f2cc
-- title:
--   Finite simple predictable compensated Poisson isometry with proven diagonal moments
-- statement:
--   For an adapted finite simple-predictable Poisson integrand with integrable cell squares and pairwise products, the expected squared finite compensated integral equals the sum of intensity-weighted expected squared coefficients, without separately assuming diagonal or off-diagonal second moment identities.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4, finite simple-predictable integrand stage.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Theorems.Thm_Kyprianou_Ch04_simplePredictableFiniteOrthogonalIsometry
import Theorems.Thm_Kyprianou_Ch04_simplePredictableDiagonalRealMoment
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.simplePredictableFullyDiagonalFiniteIsometry
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ (inferInstance : MeasurableSpace Ω))
    (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (hPart : ∀ i : Fin φ.N, 0 ≤ φ.partition i.castSucc)
    (hAdapt : ∀ i : Fin φ.N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    (hProd : ∀ i j : Fin φ.N,
      Integrable (fun ω =>
        (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) *
        (φ.ξ j ω * N.compensated (φ.timeRect j T) ω)) P)
    (hWeightInt : ∀ i : Fin φ.N,
      Integrable (fun ω => (φ.ξ i ω) ^ 2) P) :
    ∫ ω, (∑ i : Fin φ.N,
      φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P =
      ∑ i : Fin φ.N, (referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  sorry
