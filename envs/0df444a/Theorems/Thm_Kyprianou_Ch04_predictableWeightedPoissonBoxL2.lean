-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableWeightedPoissonBoxL2
-- name    : Kyprianou.Ch04.predictableWeightedPoissonBoxL2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:59:36.975209+00:00
-- url     : https://prove2.me/theorems/4744bcf3-ef39-566c-9868-3507b7e552fc
-- title:
--   Second moment of a predictable weighted compensated Poisson box
-- statement:
--   A square-integrable past-measurable weight times a finite-intensity future compensated box is square-integrable, and its second moment is the intensity times the weight second moment.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; weighted Poisson cell isometry.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_pastWeightedPoissonBoxSquareMoment
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.predictableWeightedPoissonBoxL2
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (u t : NNReal) (hut : u ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hFin : referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (H : Ω → ℝ) (hH : StronglyMeasurable[F u] H)
    (hH2 : Integrable (fun ω => (H ω)^2) P) :
    Integrable (fun ω => (H ω * N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω)^2) P ∧
    (∫ ω, (H ω * N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω)^2 ∂P) =
      (referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B)).toReal *
        ∫ ω, (H ω)^2 ∂P := by
  sorry
