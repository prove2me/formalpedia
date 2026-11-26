-- Prove2me | Theorems.Thm_Kyprianou_Ch04_sameTimeWeightedPoissonBoxCovariance
-- name    : Kyprianou.Ch04.sameTimeWeightedPoissonBoxCovariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:28:44.532813+00:00
-- url     : https://prove2.me/theorems/f956f1ea-c8d4-43ee-bdd3-ac3f3ebbc822
-- title:
--   Weighted same-time Poisson box covariance for overlapping marks
-- statement:
--   A signed integrable past-measurable weight times the product of two compensated counts over the same future time interval has expectation equal to the weight expectation times the intensity of the intersection.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; covariance of overlapping predictable rectangles.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_weightedOverlapCovarianceExpansion
import Theorems.Thm_Kyprianou_Ch04_sameTimeWeightedPoissonBoxCrossZero
import Theorems.Thm_Kyprianou_Ch04_signedWeightProductIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.sameTimeWeightedPoissonBoxCovariance
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (a t : NNReal) (hat : a ≤ t)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAf : referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤)
    (hBf : referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (W : Ω → ℝ) (hW : StronglyMeasurable[F a] W) (hWi : Integrable W P) :
    (∫ ω, W ω * N.compensated (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ω *
      N.compensated (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ B) ω ∂P) =
    (∫ ω, W ω ∂P) *
      (referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ (A ∩ B))).toReal := by
  sorry
