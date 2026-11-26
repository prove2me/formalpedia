-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedPrimitiveClockLipschitz
-- name    : Kyprianou.Ch04.boundedPrimitiveClockLipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:39:43.897796+00:00
-- url     : https://prove2.me/theorems/5ea02619-c2c6-52f0-9998-6d5c2f1380d1
-- title:
--   boundedPrimitiveClockLipschitz
-- statement:
--   A locally integrable bounded time density has a Lipschitz Lebesgue primitive.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A locally integrable bounded time density has a Lipschitz Lebesgue primitive. -/
theorem Kyprianou.Ch04.boundedPrimitiveClockLipschitz (g : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hi : ∀ t : NNReal, IntegrableOn g (Icc (0 : ℝ) (t : ℝ)) volume)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0 : ℝ)), ‖g r‖ ≤ C)
    (s t : NNReal) (hst : s ≤ t) :
    |(∫ r in Icc (0 : ℝ) (t : ℝ), g r ∂volume) -
      (∫ r in Icc (0 : ℝ) (s : ℝ), g r ∂volume)| ≤ C*((t:ℝ)-(s:ℝ)) := by
  sorry
