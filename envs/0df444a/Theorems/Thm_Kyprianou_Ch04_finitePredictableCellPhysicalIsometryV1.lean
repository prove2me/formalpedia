-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finitePredictableCellPhysicalIsometryV1
-- name    : Kyprianou.Ch04.finitePredictableCellPhysicalIsometryV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:38:02.524257+00:00
-- url     : https://prove2.me/theorems/571c5627-8a25-45a5-a252-95ad28353c11
-- title:
--   Physical isometry for finite predictable time-mark cells
-- statement:
--   Finite predictable time cells inherit the physical isometry from tail boxes.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical predictable integration.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_finitePredictableTailBoxPhysicalIsometry
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finitePredictableCellPhysicalIsometryV1 {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ →
      Measurable[F u] (fun ω => N.N ω D))
    (s : Finset ι) (T : NNReal) (a b : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i) (hbT : ∀ i ∈ s, b i ≤ T)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFa : ∀ i ∈ s, referenceIntensity ν (Ioc (a i : ℝ) (T : ℝ) ×ˢ B i) ≠ ⊤)
    (hFb : ∀ i ∈ s, referenceIntensity ν (Ioc (b i : ℝ) (T : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    let K := fun ω z => ∑ i ∈ s, (Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i).indicator
      (fun _ => H i ω) z
    let J := fun ω => (∫ z, K ω z ∂(N.N ω)) - (∫ z, K ω z ∂referenceIntensity ν)
    Integrable (fun ω => (J ω)^2) P ∧
      (∫ ω, (J ω)^2 ∂P) = ∫ ω, ∫ z, (K ω z)^2 ∂referenceIntensity ν ∂P := by
  sorry
end Kyprianou.Ch04
