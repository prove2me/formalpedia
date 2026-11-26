-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableTailRectangleCovariance
-- name    : Kyprianou.Ch04.predictableTailRectangleCovariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:39:56.799668+00:00
-- url     : https://prove2.me/theorems/09c976a6-b30c-4b1e-8c09-3d17faa0b4ad
-- title:
--   Predictable tail rectangle covariance
-- statement:
--   The covariance of two predictable weighted compensated Poisson tail boxes equals the expected product of their weights multiplied by the reference intensity of their common time-mark rectangle.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; predictable isometry extension.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_orderedPredictableTailRectangleCovariance
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.predictableTailRectangleCovariance
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (a b t : NNReal) (hat : a ≤ t) (hbt : b ≤ t)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAf : referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤)
    (hBf : referenceIntensity ν (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (H K : Ω → ℝ) (hH : StronglyMeasurable[F a] H) (hK : StronglyMeasurable[F b] K)
    (hH2 : Integrable (fun ω => (H ω)^2) P)
    (hK2 : Integrable (fun ω => (K ω)^2) P) :
    (∫ ω, (H ω * N.compensated (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ω) *
      (K ω * N.compensated (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ B) ω) ∂P) =
      (∫ ω, H ω * K ω ∂P) *
      (referenceIntensity ν (Set.Ioc (↑(max a b) : ℝ) (t : ℝ) ×ˢ (A ∩ B))).toReal := by
  sorry
