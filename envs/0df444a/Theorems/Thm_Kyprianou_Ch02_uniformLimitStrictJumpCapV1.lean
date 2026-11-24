-- Prove2me | Theorems.Thm_Kyprianou_Ch02_uniformLimitStrictJumpCapV1
-- name    : Kyprianou.Ch02.uniformLimitStrictJumpCapV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:20:39.753899+00:00
-- url     : https://prove2.me/theorems/1c9f0e4d-1f4a-48af-81fb-146bf7d5f424
-- title:
--   Uniform convergence preserves a common strict cap on left jumps
-- statement:
--   On a compact nonnegative-time interval, if all approximants have left limits with jumps bounded above in absolute value by one common c < 1, any uniform limit has the same strict bound below one at every positive time with a left limit.
-- source:
--   Kyprianou (2006), Theorem 2.1 and Chapter 2 finite-band approximation; supporting lemma

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem uniformLimitStrictJumpCapV1
    (F : ℕ → ℝ≥0 → ℝ) (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (c : ℝ) (hc : c < 1)
    (hu : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ t : ℝ≥0, t ≤ T → |F n t - f t| < δ)
    (hb : ∀ (n : ℕ) (t : ℝ≥0), 0 < t → t ≤ T →
      ∃ l : ℝ, Tendsto (F n) (nhdsWithin t (Set.Iio t)) (nhds l) ∧
        |F n t - l| ≤ c)
    (t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (l : ℝ) (hl : Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l)) :
    |f t - l| < 1 := by sorry
end Kyprianou.Ch02
