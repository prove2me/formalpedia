-- Prove2me | Theorems.Thm_Kyprianou_Ch04_fullPredictablePhysicalL2Core
-- name    : Kyprianou.Ch04.fullPredictablePhysicalL2Core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:43:42.079941+00:00
-- url     : https://prove2.me/theorems/a0950552-71ab-4f31-be50-985d33a829ac
-- title:
--   Full predictable physical L2 isometry
-- statement:
--   The full physical compensated Poisson integral of a predictable L1 and L2 kernel obeys the isometry on the entire mark space.
-- source:
--   Kyprianou (2006), Exercise 4.4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The full physical compensated Poisson isometry for integrable predictable L2 kernels. -/
theorem Kyprianou.Ch04.fullPredictablePhysicalL2Core
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
    (hPast : ∀ (u : NNReal) (E : Set (ℝ × ℝ)), MeasurableSet E →
      E ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun w => N.N w E))
    (t : NNReal)
    [mAll : MeasurableSpace ((NNReal × Omega) × ℝ)]
    (hAll : mAll = F.predictable.prod (inferInstance : MeasurableSpace ℝ))
    (mu : Measure ((NNReal × Omega) × ℝ))
    (hClock : ∀ f : ((NNReal × Omega) × ℝ) → ENNReal, Measurable f →
      AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂(N.N w)) P ∧
      AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu) P ∧
      (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂(N.N w) ∂P) ∧
      (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P))
    (g : ((NNReal × Omega) × ℝ) → ℝ) (hgm : Measurable g)
    (hgi : Integrable g mu) (hg : MemLp g 2 mu) :
    let V := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
    let X := fun w => (∫ z in V, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in V, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu
    Integrable (fun w => (X w)^2) P ∧
      (∫ w, (X w)^2 ∂P) = ∫ w, ∫ z in V,
        (g ((z.1.toNNReal,w),z.2))^2 ∂referenceIntensity nu ∂P := by
  sorry
