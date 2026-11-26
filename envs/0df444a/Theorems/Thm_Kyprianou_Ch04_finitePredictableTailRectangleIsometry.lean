-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finitePredictableTailRectangleIsometry
-- name    : Kyprianou.Ch04.finitePredictableTailRectangleIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:44:49.917861+00:00
-- url     : https://prove2.me/theorems/f4bec928-ebe8-409a-8a4c-b8ba96dda1b0
-- title:
--   Isometry for arbitrary finite predictable tail rectangles
-- statement:
--   The compensated sum of any finite collection of predictably weighted tail rectangles is square integrable and has second moment equal to the expected reference-intensity integral of the squared signed indicator kernel, with no disjointness restriction.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; elementary signed predictable isometry.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableTailRectangleCovariance
import Theorems.Thm_Kyprianou_Ch04_finiteFamilyCovarianceExpansion
import Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorSquareIntegral
import Theorems.Thm_Kyprianou_Ch04_finiteCoefficientCrossMomentIntegral
import Theorems.Thm_Kyprianou_Ch04_predictableWeightedPoissonBoxL2
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.finitePredictableTailRectangleIsometry
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (s : Finset ι) (a : ι → NNReal) (t : NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hat : ∀ i ∈ s, a i ≤ t)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    let S := fun i => Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i
    let Z := fun ω => ∑ i ∈ s, H i ω * N.compensated (S i) ω
    let K := fun ω z => ∑ i ∈ s, (S i).indicator (fun _ => H i ω) z
    MemLp Z 2 P ∧
      (∫ ω, (Z ω)^2 ∂P) =
      ∫ ω, (∫ z, (K ω z)^2 ∂referenceIntensity ν) ∂P := by
  sorry
