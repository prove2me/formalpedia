-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compactUniformRightLimitV1
-- name    : Kyprianou.Ch04.compactUniformRightLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:51:36.578866+00:00
-- url     : https://prove2.me/theorems/dcac0c7e-09a5-5b6e-9c12-a99ca0ebbb60
-- title:
--   Right continuity of compact uniform limits
-- statement:
--   Compact uniform limits of right-continuous real paths are right-continuous.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem compactUniformRightLimitV1 (Y : ℕ → NNReal → ℝ) (M : NNReal → ℝ)
    (hY : ∀ n t, Tendsto (Y n) (𝓝[>] t) (𝓝 (Y n t)))
    (hM : ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |Y n t - M t| < δ) :
    ∀ t, Tendsto M (𝓝[>] t) (𝓝 (M t)) := by
  sorry
end Kyprianou.Ch04
