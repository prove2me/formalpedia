-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42AffineSecondCoordinateLipschitzV1
-- name    : Kyprianou.Ch04.exercise42AffineSecondCoordinateLipschitzV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:24:00.534397+00:00
-- url     : https://prove2.me/theorems/7f6fb6aa-1adf-5ed9-b73c-e0970a4a29ff
-- title:
--   Affine scalar coordinate is Lipschitz with its drift norm
-- statement:
--   The scalar affine function s ↦ a+c*s is Lipschitz, with exact Lipschitz bound equal to the absolute value of c.
-- source:
--   Deterministic first step for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An affine scalar path has Lipschitz constant equal to the norm of its drift. -/

theorem Kyprianou.Ch04.exercise42AffineSecondCoordinateLipschitzV1 (a c : ℝ) :
    LipschitzWith ‖c‖₊ (fun t : ℝ => a + c * t) := by
  sorry
