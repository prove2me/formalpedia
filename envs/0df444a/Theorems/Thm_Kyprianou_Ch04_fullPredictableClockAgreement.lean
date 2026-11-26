-- Prove2me | Theorems.Thm_Kyprianou_Ch04_fullPredictableClockAgreement
-- name    : Kyprianou.Ch04.fullPredictableClockAgreement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:39:16.020016+00:00
-- url     : https://prove2.me/theorems/13d608bc-6d7d-5964-997b-07ec9b47a8b2
-- title:
--   Full predictable clock agreement
-- statement:
--   Full predictable expected clock agreement between the physical Poisson random measure and its reference intensity on a finite time horizon.
-- source:
--   Kyprianou (2006), Exercise 4.4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The full predictable expected clock measure represents both raw and intensity integrals. -/
theorem Kyprianou.Ch04.fullPredictableClockAgreement
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N) (t : NNReal) :
    let m := F.predictable.prod (inferInstance : MeasurableSpace ℝ)
    ∃ mu : @Measure ((NNReal × Omega) × ℝ) m,
      ∀ f : ((NNReal × Omega) × ℝ) → ENNReal, Measurable[m] f →
        AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
          f ((z.1.toNNReal,w),z.2) ∂(N.N w)) P ∧
        AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
          f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu) P ∧
        (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
          f ((z.1.toNNReal,w),z.2) ∂(N.N w) ∂P) ∧
        (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
          f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P) := by
  sorry
