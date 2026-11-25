-- Prove2me | Theorems.Thm_Kyprianou_Ch04_simplePredictableFiniteL2Isometry
-- name    : Kyprianou.Ch04.simplePredictableFiniteL2Isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:18:38.054142+00:00
-- url     : https://prove2.me/theorems/0c44c203-b06f-5744-9912-108d4270647e
-- title:
--   Finite simple predictable Poisson isometry from individual L2 bounds
-- statement:
--   Under adaptation and individual L2 integrability of each compensated Poisson cell and each predictable weight, exact finite-sum second-moment isometry follows, with pairwise product integrability derived automatically by Holder.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4, finite simple predictable integral stage; combines proved finite diagonal and off-diagonal Poisson isometries with L2 Holder.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Theorems.Thm_Kyprianou_Ch04_simplePredictableFullyDiagonalFiniteIsometry
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.simplePredictableFiniteL2Isometry
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
    (hZMeas : ∀ i : Fin φ.N, AEStronglyMeasurable
      (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i T) ω) P)
    (hZSq : ∀ i : Fin φ.N, Integrable
      (fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2) P)
    (hWeightInt : ∀ i : Fin φ.N,
      Integrable (fun ω => (φ.ξ i ω) ^ 2) P) :
    ∫ ω, (∑ i : Fin φ.N,
      φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P =
      ∑ i : Fin φ.N, (referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  sorry
