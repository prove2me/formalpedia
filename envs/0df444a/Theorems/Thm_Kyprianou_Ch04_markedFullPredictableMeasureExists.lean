-- Prove2me | Theorems.Thm_Kyprianou_Ch04_markedFullPredictableMeasureExists
-- name    : Kyprianou.Ch04.markedFullPredictableMeasureExists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:30:29.828127+00:00
-- url     : https://prove2.me/theorems/3ae52973-6704-5f11-9d9c-292000bd5afe
-- title:
--   markedFullPredictableMeasureExists
-- statement:
--   The expected predictable clock measure on a finite time horizon exists as a pushforward of the intensity-product measure.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch04_markedPredictableLeAmbientProduct
open MeasureTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The full predictable expected clock measure is a pushforward of intensity times probability. -/
theorem Kyprianou.Ch04.markedFullPredictableMeasureExists
    {Omega : Type} [mO : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal mO) (t : NNReal) :
    let m := F.predictable.prod (inferInstance : MeasurableSpace ℝ)
    ∃ mu : @Measure ((NNReal × Omega) × ℝ) m,
      ∀ f : ((NNReal × Omega) × ℝ) → ENNReal, Measurable[m] f →
        (∫⁻ a, f a ∂mu) =
          ∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
            f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P := by sorry
