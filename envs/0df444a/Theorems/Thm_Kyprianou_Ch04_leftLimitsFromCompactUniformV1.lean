-- Prove2me | Theorems.Thm_Kyprianou_Ch04_leftLimitsFromCompactUniformV1
-- name    : Kyprianou.Ch04.leftLimitsFromCompactUniformV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:20:36.061813+00:00
-- url     : https://prove2.me/theorems/2be32ece-8074-472a-8fc3-f52565914532
-- title:
--   Compact uniform convergence passes to positive-time left limits
-- statement:
--   Compact uniform convergence passes to positive-time left limits.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem leftLimitsFromCompactUniformV1 (U L : ℕ → NNReal → ℝ) (X Y : NNReal → ℝ)
    (hU : ∀ n t, 0 < t → Tendsto (U n) (𝓝[<] t) (𝓝 (L n t)))
    (hX : ∀ t, 0 < t → Tendsto X (𝓝[<] t) (𝓝 (Y t)))
    (h : ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |U n t - X t| < δ) :
    ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal, 0 < t → t ≤ T → |L n t - Y t| < δ := by
  sorry
end Kyprianou.Ch04
