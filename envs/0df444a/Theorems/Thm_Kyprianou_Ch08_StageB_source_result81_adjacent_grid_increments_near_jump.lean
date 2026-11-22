-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_adjacent_grid_increments_near_jump
-- name    : Kyprianou.Ch08.StageB.source_result81_adjacent_grid_increments_near_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:58:51.477742+00:00
-- url     : https://prove2.me/theorems/5766e10b-5ac4-4ca0-8552-cf2d47b9680c
-- title:
--   Adjacent grid increments converge across a positive jump
-- statement:
--   The grid interval whose left endpoint is strictly below a positive jump and whose right endpoint is at or above it detects the jump on all sufficiently fine grids. The increment exceeds any threshold tending to zero.
-- source:
--   Auxiliary lemma for the spectral-negativity step in Kyprianou (2006), Chapter 8, Theorem 8.1. Parent Prove2Me theorem 92200ffc-acdc-4836-b709-dd420298cdde.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_adjacent_grid_increments_near_jump
    (f : ℝ≥0 → ℝ) (d : ℕ → ℝ≥0) (hd : ∀ n, 0 < d n)
    (hd0 : Tendsto d atTop (𝓝 0)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (M : ℕ) (t : ℝ≥0) (l : ℝ) (ht : 0 < t) (hM : t ≤ M)
    (hR : ContinuousWithinAt f (Ici t) t) (hL : Tendsto f (𝓝[<] t) (𝓝 l))
    (hj : l < f t) :
    ∀ᶠ n in atTop, ∃ k < ⌈(M : ℝ≥0) / d n⌉₊,
      ε n ≤ f ((k : ℝ≥0) * d n + d n) - f ((k : ℝ≥0) * d n) := by
  sorry
