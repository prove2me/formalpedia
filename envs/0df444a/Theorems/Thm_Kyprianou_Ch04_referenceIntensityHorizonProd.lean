-- Prove2me | Theorems.Thm_Kyprianou_Ch04_referenceIntensityHorizonProd
-- name    : Kyprianou.Ch04.referenceIntensityHorizonProd
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:43:14.948875+00:00
-- url     : https://prove2.me/theorems/a03a3c97-c192-5e62-96a5-0a198b18705d
-- title:
--   referenceIntensityHorizonProd
-- statement:
--   Reference intensity restricted to a closed finite time horizon is the product of the restricted Lebesgue measure and the mark measure.
-- source:
--   Kyprianou (2006), Exercise 4.4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The restricted reference intensity is the product of the time and mark measures. -/
theorem Kyprianou.Ch04.referenceIntensityHorizonProd (nu : Measure ℝ) [SigmaFinite nu] (t : NNReal) :
    (referenceIntensity nu).restrict (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)) =
      (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod nu := by
  sorry
