-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteWeightedPoissonCellIsometry
-- name    : Kyprianou.Ch04.finiteWeightedPoissonCellIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:59:41.86304+00:00
-- url     : https://prove2.me/theorems/9dcb2f49-2859-44c3-a2f6-61626d6af9a9
-- title:
--   L2 isometry for finite orthogonal independent weighted Poisson cells
-- statement:
--   A finite family of square-integrable independent weights multiplied by compensated Poisson counts has expected squared sum equal to the sum of intensity-weighted expected squared weights, whenever pairwise mixed products are integrable and their off-diagonal expectations vanish.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4, finite simple-predictable integrand stage; combines proved diagonal compensated-cell second moments and orthogonal finite-square expansion.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_orthogonalFiniteFamilyL2Identity
import Theorems.Thm_Kyprianou_Ch04_independentWeightedPoissonCellIsometry
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.finiteWeightedPoissonCellIsometry
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    {ι : Type} [DecidableEq ι]
    (s : Finset ι) (B : ι → Set (ℝ × ℝ)) (H : ι → Ω → ℝ)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (B i) ≠ ⊤)
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω) ^ 2) P)
    (hIndep : ∀ i ∈ s, IndepFun (H i) (fun ω => N.N ω (B i)) P)
    (hProd : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => (H i ω * N.compensated (B i) ω) *
        (H j ω * N.compensated (B j) ω)) P)
    (hOrth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∫ ω, (H i ω * N.compensated (B i) ω) *
        (H j ω * N.compensated (B j) ω) ∂P = 0) :
    ∫ ω, (∑ i ∈ s, H i ω * N.compensated (B i) ω) ^ 2 ∂P =
      ∑ i ∈ s, (referenceIntensity ν (B i)).toReal *
        ∫ ω, (H i ω) ^ 2 ∂P := by
  sorry
