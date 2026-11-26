-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedPredictablePhysicalPastEventIncrementV1
-- name    : Kyprianou.Ch04.boundedPredictablePhysicalPastEventIncrementV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:41:30.265643+00:00
-- url     : https://prove2.me/theorems/36e998a1-3f54-55e4-8b53-b0538b61154a
-- title:
--   Conditional centring of bounded supported predictable physical increments
-- statement:
--   Mask a bounded predictable kernel by a past measurable event and the future time interval. Compensation gives expectation zero, and the exact interval increment formula gives equal past-event set integrals.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedPredictablePhysicalPastEventIncrementV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal inferInstance) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ p, ‖g p‖ ≤ C)
    (hsupp : ∀ p, p.2 ∉ B → g p = 0)
    (s t : NNReal) (hst : s ≤ t) (A : Set Ω) (hA : MeasurableSet[F s] A)
    (hi : ∀ᵐ w ∂P,
      IntegrableOn (fun z : ℝ × ℝ => g ((z.1.toNNReal,w),z.2))
        (Icc (0 : ℝ) (t : ℝ) ×ˢ univ) (N.N w) ∧
      IntegrableOn (fun z : ℝ × ℝ => g ((z.1.toNNReal,w),z.2))
        (Icc (0 : ℝ) (t : ℝ) ×ˢ univ) (referenceIntensity ν)) :
    let J := fun (u : NNReal) w =>
      (∫ z in Icc (0 : ℝ) (u : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in Icc (0 : ℝ) (u : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
    (∫ w in A, J s w ∂P) = ∫ w in A, J t w ∂P := by
  sorry
end Kyprianou.Ch04
