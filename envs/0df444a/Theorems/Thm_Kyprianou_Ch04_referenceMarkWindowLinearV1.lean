-- Prove2me | Theorems.Thm_Kyprianou_Ch04_referenceMarkWindowLinearV1
-- name    : Kyprianou.Ch04.referenceMarkWindowLinearV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:41:34.977062+00:00
-- url     : https://prove2.me/theorems/1dcc3e22-6c1f-51a6-80c3-90f3dd136f7d
-- title:
--   referenceMarkWindowLinearV1
-- statement:
--   Physical clipped grid integral identity.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_referenceIntensityClosedWindowProductV1
import Theorems.Thm_Kyprianou_Ch04_physicalMarkIndicatorWindowIntegralV1
open MeasureTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The compensator of a marked window with a time-independent mark kernel is
its clock length times the mark integral. -/

theorem Kyprianou.Ch04.referenceMarkWindowLinearV1 (ν : Measure ℝ) [SigmaFinite ν] (t : NNReal)
    (B : Set ℝ) (hB : MeasurableSet B) (Q : ℝ → ℝ) :
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
      B.indicator Q z.2 ∂ referenceIntensity ν) =
      (t : ℝ) * (∫ x in B,Q x ∂ν) := by
  sorry
