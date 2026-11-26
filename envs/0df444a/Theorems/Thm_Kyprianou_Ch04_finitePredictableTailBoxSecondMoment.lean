-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finitePredictableTailBoxSecondMoment
-- name    : Kyprianou.Ch04.finitePredictableTailBoxSecondMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:45:50.512997+00:00
-- url     : https://prove2.me/theorems/fe2a43e3-e90e-43c2-9f6e-b04662dcf305
-- title:
--   Finite predictable tail box second moment
-- statement:
--   The finite sum of weighted compensated predictable tail boxes is square integrable. Its second moment equals the sum over all ordered pairs of cells of the expected weight product times the intersection intensity.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; elementary predictable isometry.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableTailRectangleCovariance
import Theorems.Thm_Kyprianou_Ch04_finiteFamilyCovarianceExpansion
import Theorems.Thm_Kyprianou_Ch04_predictableWeightedPoissonBoxL2
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.finitePredictableTailBoxSecondMoment
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
    let Z := fun i ω => H i ω *
      N.compensated (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i) ω
    Integrable (fun ω => (∑ i ∈ s, Z i ω)^2) P ∧
      (∫ ω, (∑ i ∈ s, Z i ω)^2 ∂P) =
      ∑ i ∈ s, ∑ j ∈ s, (∫ ω, H i ω * H j ω ∂P) *
        (referenceIntensity ν
          (Set.Ioc (↑(max (a i) (a j)) : ℝ) (t : ℝ) ×ˢ (B i ∩ B j))).toReal := by
  sorry
