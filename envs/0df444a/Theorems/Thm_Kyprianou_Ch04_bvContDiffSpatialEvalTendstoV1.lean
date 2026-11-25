-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvContDiffSpatialEvalTendstoV1
-- name    : Kyprianou.Ch04.bvContDiffSpatialEvalTendstoV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:31:36.955305+00:00
-- url     : https://prove2.me/theorems/d45a5aec-9f97-4ebb-bdaa-3a4239fd36b0
-- title:
--   Continuous evaluation at a fixed nonnegative time
-- statement:
--   Restrict the continuous test function to a vertical line in the half-plane, then compose its continuity with the given limit.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; compact deterministic estimates.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvContDiffSpatialEvalTendstoV1
    {I : Type} (L : Filter I)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (u : ℝ) (hu : 0 ≤ u) (G : I → ℝ) (g : ℝ)
    (h : Tendsto G L (nhds g)) :
    Tendsto (fun i => f (u,G i)) L (nhds (f (u,g))) := by
  sorry
