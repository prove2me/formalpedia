-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvCompactSpatialLipschitzV1
-- name    : Kyprianou.Ch04.bvCompactSpatialLipschitzV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:31:34.70799+00:00
-- url     : https://prove2.me/theorems/0a165779-8d42-4dd1-bb2a-d7312f05abc0
-- title:
--   Uniform spatial mean-value bound on a compact space-time rectangle
-- statement:
--   The continuous half-plane derivative is bounded on the compact rectangle. Restrict its derivative to that convex rectangle and apply the mean-value inequality. The two points have equal time coordinate.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; compact deterministic estimates.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvCompactSpatialLipschitzV1
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (T M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u x y : ℝ),
      u ∈ Set.Icc 0 T → x ∈ Set.Icc (-M) M → y ∈ Set.Icc (-M) M →
      |f (u,x) - f (u,y)| ≤ C * |x-y| := by
  sorry
