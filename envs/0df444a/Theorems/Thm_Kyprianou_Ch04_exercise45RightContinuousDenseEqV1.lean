-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45RightContinuousDenseEqV1
-- name    : Kyprianou.Ch04.exercise45RightContinuousDenseEqV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:32:25.533042+00:00
-- url     : https://prove2.me/theorems/739cd46d-40c4-515a-a335-06d909c278be
-- title:
--   Right-continuous dense-grid uniqueness
-- statement:
--   Right-continuous real functions agree everywhere when they agree on a dense sequence.
-- source:
--   Kyprianou Exercise 4.5, reconstruction

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal
set_option autoImplicit false

/-- Two right-continuous functions agreeing on a dense grid agree everywhere. -/
theorem Kyprianou.Ch04.exercise45RightContinuousDenseEqV1 (f g : NNReal → ℝ) (grid : ℕ → NNReal) (hd : DenseRange grid)
    (hf : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hg : ∀ t, ContinuousWithinAt g (Ici t) t)
    (he : ∀ k, f (grid k) = g (grid k)) : ∀ t, f t = g t := by
  sorry
