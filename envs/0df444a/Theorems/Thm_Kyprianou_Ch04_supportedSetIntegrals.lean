-- Prove2me | Theorems.Thm_Kyprianou_Ch04_supportedSetIntegrals
-- name    : Kyprianou.Ch04.supportedSetIntegrals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:39:46.951161+00:00
-- url     : https://prove2.me/theorems/f21f4680-e88d-4461-a5e1-497f7aa3c09a
-- title:
--   supportedSetIntegrals
-- statement:
--   A real kernel vanishing outside a smaller measurable set has identical integrals over the two nested measurable sets.
-- source:
--   Kyprianou (2006), Exercise 4.4

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

/-- A kernel vanishing outside a smaller set has the same integral on either set. -/
theorem Kyprianou.Ch04.supportedSetIntegrals {E : Type} [MeasurableSpace E] (mu : Measure E)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V)
    (f : E → ℝ) (hz : ∀ z ∈ V, z ∉ U → f z = 0) :
    (∫ z in V, f z ∂mu) = ∫ z in U, f z ∂mu := by
  sorry
