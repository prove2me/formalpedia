-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finitePredictableTailBoxPhysicalIsometry
-- name    : Kyprianou.Ch04.finitePredictableTailBoxPhysicalIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:52:39.743068+00:00
-- url     : https://prove2.me/theorems/80923231-34c7-4c72-8780-bf5b0cf2cf22
-- title:
--   Physical compensated isometry for finite predictable tail boxes
-- statement:
--   For any finite signed predictable weighted tail-box kernel, with finite cell intensities and square-integrable coefficients, the physical compensated integral is square integrable and its second moment equals the expected intensity energy. Overlapping time-mark rectangles are allowed.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; elementary predictable isometry.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finitePredictableTailBoxSecondMoment
import Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorExpectedSquareIntegral
import Theorems.Thm_Kyprianou_Ch04_finitePoissonIndicatorIntegralAE
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.finitePredictableTailBoxPhysicalIsometry
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (s : Finset ι) (t : NNReal) (a : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hat : ∀ i ∈ s, a i ≤ t)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    let C := fun i => Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i
    let K := fun ω z => ∑ i ∈ s, (C i).indicator (fun _ => H i ω) z
    let X := fun ω => (∫ z, K ω z ∂(N.N ω)) -
      (∫ z, K ω z ∂referenceIntensity ν)
    Integrable (fun ω => (X ω)^2) P ∧
      (∫ ω, (X ω)^2 ∂P) = ∫ ω, ∫ z, (K ω z)^2 ∂referenceIntensity ν ∂P := by
  sorry
