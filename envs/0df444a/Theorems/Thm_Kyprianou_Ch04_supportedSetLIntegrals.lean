-- Prove2me | Theorems.Thm_Kyprianou_Ch04_supportedSetLIntegrals
-- name    : Kyprianou.Ch04.supportedSetLIntegrals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:39:44.945531+00:00
-- url     : https://prove2.me/theorems/7133eab2-ddf0-5bc1-887e-8d1381902c50
-- title:
--   supportedSetLIntegrals
-- statement:
--   An extended nonnegative kernel supported on a smaller measurable set has identical lintegrals over the two nested sets.
-- source:
--   Kyprianou (2006), Exercise 4.4

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

/-- Nonnegative integral equality on nested sets for a supported kernel. -/
theorem Kyprianou.Ch04.supportedSetLIntegrals {E : Type} [MeasurableSpace E] (mu : Measure E)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V)
    (f : E → ENNReal) (hz : ∀ z ∈ V, z ∉ U → f z = 0) :
    (∫⁻ z in V, f z ∂mu) = ∫⁻ z in U, f z ∂mu := by
  sorry
