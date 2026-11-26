-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteBandPredictableClockAgreement
-- name    : Kyprianou.Ch04.finiteBandPredictableClockAgreement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:49:52.846215+00:00
-- url     : https://prove2.me/theorems/57bb0eea-88b8-5247-9648-ed48c47ef9bd
-- title:
--   Finite predictable clock agreement
-- statement:
--   The finite predictable clock measure simultaneously represents the expected nonnegative raw and intensity integrals, with almost-everywhere measurable clocks.
-- source:
--   Kyprianou (2006), Exercise 4.4, supporting physical L1 approximation lemma.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteMarkedClockMeasure
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
import Theorems.Thm_Kyprianou_Ch04_predictableRectangleCountFactorisation
import Theorems.Thm_Kyprianou_Ch04_predictableCompensationFiniteBandFromRectangleCounts
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The finite predictable clock measure represents both random and intensity integrals. -/
theorem Kyprianou.Ch04.finiteBandPredictableClockAgreement
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure Real) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
    (t : NNReal) (B : Set Real) (hB : MeasurableSet B) (hBfin : nu B < ⊤) :
    let m := F.predictable.prod (inferInstance : MeasurableSpace Real)
    ∃ mu : @Measure ((NNReal × Omega) × Real) m,
      IsFiniteMeasure mu ∧
      ∀ f : ((NNReal × Omega) × Real) → ENNReal, Measurable[m] f →
        AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
          f ((z.1.toNNReal,w),z.2) ∂(N.N w)) P ∧
        AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
          f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu) P ∧
        (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
          f ((z.1.toNNReal,w),z.2) ∂(N.N w) ∂P) ∧
        (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
          f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P) := by
  sorry
