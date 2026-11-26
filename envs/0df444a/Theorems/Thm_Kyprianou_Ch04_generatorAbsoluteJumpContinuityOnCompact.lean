-- Prove2me | Theorems.Thm_Kyprianou_Ch04_generatorAbsoluteJumpContinuityOnCompact
-- name    : Kyprianou.Ch04.generatorAbsoluteJumpContinuityOnCompact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:05:07.838924+00:00
-- url     : https://prove2.me/theorems/d7776133-6b9b-4029-82a6-e49c1ffe8e6b
-- title:
--   Local continuity of absolute jump mass
-- statement:
--   Local continuity of absolute jump mass.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter Set Topology
set_option autoImplicit false

/-- Local integrable jump envelopes imply continuity of the absolute jump mass. -/
theorem Kyprianou.Ch04.generatorAbsoluteJumpContinuityOnCompact (nu : Measure ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b nu ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂nu, ‖f (z+x)-f z‖ ≤ b x) :
    Continuous (fun y => ∫ x, ‖f (y+x)-f y‖ ∂nu) := by
  sorry
