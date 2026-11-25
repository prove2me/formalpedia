-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineACV1
-- name    : Kyprianou.Ch04.exercise42LipschitzAffineACV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T18:25:37.336322+00:00
-- url     : https://prove2.me/theorems/488f488a-99c6-4464-a261-44b42107b13a
-- title:
--   Compact-interval absolute continuity of a C1 affine/Lipschitz composition
-- statement:
--   A C1 function applied to a Lipschitz nonnegative path and an affine coordinate is absolutely continuous on any compact interval where the first coordinate remains nonnegative.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.2, printed page 106.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzAffineACV1
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ) (hlr : l ≤ r)
    (hpos : ∀ s ∈ Icc l r, 0 ≤ U s) :
    AbsolutelyContinuousOnInterval (fun s : ℝ => f (U s, a + c * s)) l r := by
  sorry
