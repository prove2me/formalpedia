-- Prove2me | Theorems.Thm_Kyprianou_Ch04_generatorJumpContinuityOnCompact
-- name    : Kyprianou.Ch04.generatorJumpContinuityOnCompact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:07:09.490474+00:00
-- url     : https://prove2.me/theorems/ee02e6a7-ba78-4349-a3fe-d3e71f08b531
-- title:
--   generatorJumpContinuityOnCompact
-- statement:
--   Local integrable envelopes for the jump differences of a continuous function imply continuity of the signed jump generator.
-- source:
--   Kyprianou (2006), Exercise 4.3(i), pp. 106-107.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter Set Topology
set_option autoImplicit false

/-- Local integrable jump envelopes imply continuity of the signed generator. -/
theorem Kyprianou.Ch04.generatorJumpContinuityOnCompact (nu : Measure ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b nu ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂nu, ‖f (z+x)-f z‖ ≤ b x) :
    Continuous (fun y => ∫ x, (f (y+x)-f y) ∂nu) := by
  sorry
