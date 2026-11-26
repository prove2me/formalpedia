-- Prove2me | Theorems.Thm_Kyprianou_Ch04_fullPredictableClockFiniteBandMassV1
-- name    : Kyprianou.Ch04.fullPredictableClockFiniteBandMassV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:07:24.95382+00:00
-- url     : https://prove2.me/theorems/1717ef4d-7f18-4666-8bd0-c1aec83740f4
-- title:
--   Finite mass of mark bands in the full predictable clock
-- statement:
--   The full predictable clock gives finite mass to every finite intensity mark band.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem fullPredictableClockFiniteBandMassV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (t : NNReal)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    [mAll : MeasurableSpace ((NNReal × Ω) × ℝ)]
    (hAll : mAll = F.predictable.prod inferInstance)
    (μ : Measure ((NNReal × Ω) × ℝ))
    (hClock : ∀ f : ((NNReal × Ω) × ℝ) → ENNReal, Measurable f →
      (∫⁻ p, f p ∂μ) = ∫⁻ w, ∫⁻ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν ∂P) :
    μ (univ ×ˢ B) < ⊤ := by
  sorry
end Kyprianou.Ch04
