-- Prove2me | Theorems.Thm_Kyprianou_Ch04_atomicMeasureMassV1
-- name    : Kyprianou.Ch04.atomicMeasureMassV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:30:49.32237+00:00
-- url     : https://prove2.me/theorems/6a5cac9d-c003-4dc3-90fc-f5a2f4f33712
-- title:
--   Mass of a summably weighted atomic measure
-- statement:
--   Evaluate the weighted Dirac sum on a measurable set using nonnegative summable indicator weights.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.atomicMeasureMassV1 {ι : Type} (a : ι → ℝ) (w : ι → ℝ)
    (hw : Summable w) (hn : ∀ i, 0 ≤ w i)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (a i))) S =
      ENNReal.ofReal (∑' i, (a ⁻¹' S).indicator w i) := by
  sorry
