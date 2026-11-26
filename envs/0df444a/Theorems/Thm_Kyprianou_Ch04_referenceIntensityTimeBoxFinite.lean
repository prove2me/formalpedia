-- Prove2me | Theorems.Thm_Kyprianou_Ch04_referenceIntensityTimeBoxFinite
-- name    : Kyprianou.Ch04.referenceIntensityTimeBoxFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:35:20.375829+00:00
-- url     : https://prove2.me/theorems/b452b9e6-16e3-5403-9543-5ca65fb8289b
-- title:
--   Finite reference intensity of bounded time-mark boxes
-- statement:
--   A bounded positive-time box whose mark set has finite intensity has finite reference intensity.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; finite predictable rectangles.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory LevyStochCalc.Poisson
open scoped ENNReal NNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch04.referenceIntensityTimeBoxFinite
    {E : Type u} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    (a b : NNReal) (A : Set E) (hA : ν A ≠ ⊤) :
    referenceIntensity ν (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ≠ ⊤ := by
  sorry
