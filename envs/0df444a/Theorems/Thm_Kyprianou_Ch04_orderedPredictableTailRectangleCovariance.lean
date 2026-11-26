-- Prove2me | Theorems.Thm_Kyprianou_Ch04_orderedPredictableTailRectangleCovariance
-- name    : Kyprianou.Ch04.orderedPredictableTailRectangleCovariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:33:07.151307+00:00
-- url     : https://prove2.me/theorems/ca6b48d6-ea4e-5eb6-aa24-9be6cc2697d4
-- title:
--   Ordered predictable tail rectangle covariance
-- statement:
--   The covariance of two predictable weighted compensated Poisson tail boxes with ordered starting times equals the expected product of their weights multiplied by the reference intensity of the common time-mark box.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; overlapping predictable rectangle covariance.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_compensatedTimeBoxSplitAE
import Theorems.Thm_Kyprianou_Ch04_sameTimeWeightedPoissonBoxCovariance
import Theorems.Thm_Kyprianou_Ch04_orderedWeightedPoissonBoxCrossZero
import Theorems.Thm_Kyprianou_Ch04_predictableWeightedPoissonBoxL2
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.orderedPredictableTailRectangleCovariance
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (a b t : NNReal) (hab : a ≤ b) (hbt : b ≤ t)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAf : referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤)
    (hBf : referenceIntensity ν (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (H K : Ω → ℝ) (hH : StronglyMeasurable[F a] H) (hK : StronglyMeasurable[F b] K)
    (hH2 : Integrable (fun ω => (H ω)^2) P)
    (hK2 : Integrable (fun ω => (K ω)^2) P) :
    (∫ ω, (H ω * N.compensated (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ω) *
      (K ω * N.compensated (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ B) ω) ∂P) =
      (∫ ω, H ω * K ω ∂P) *
      (referenceIntensity ν (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ (A ∩ B))).toReal := by
  sorry
