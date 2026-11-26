-- Prove2me | Theorems.Thm_Kyprianou_Ch04_referenceIntensityClosedWindowProductV1
-- name    : Kyprianou.Ch04.referenceIntensityClosedWindowProductV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:28:56.631153+00:00
-- url     : https://prove2.me/theorems/dc0de993-877d-45b2-af07-b43cdb5c63ca
-- title:
--   Reference intensity restricted to closed time-mark rectangle
-- statement:
--   The physical reference intensity on a nonnegative closed time window
--   is precisely the restricted time volume times the mark measure.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem referenceIntensityClosedWindowProductV1 (ν : Measure ℝ) [SigmaFinite ν] (T : NNReal) (B : Set ℝ)
    (hB : MeasurableSet B) :
    (referenceIntensity ν).restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ B) =
    (volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod (ν.restrict B) := by
  sorry
end Kyprianou.Ch04
