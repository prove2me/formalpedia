-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvHorizonRightJumpSeriesV1
-- name    : Kyprianou.Ch04.bvHorizonRightJumpSeriesV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:28:14.46195+00:00
-- url     : https://prove2.me/theorems/7822d0de-bc85-4f8d-906d-e5be9d8a1f1a
-- title:
--   Reindex the right jump series onto a fixed larger horizon
-- statement:
--   Use indicator series on the ambient nonnegative time type; restricting to the smaller horizon is equivalent to zeroing the summands after that horizon.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic absolutely summable jump approximation.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvHorizonRightJumpSeriesV1
    (g : NNReal → ℝ) (u t : NNReal) (hu : u ≤ t) :
    (∑' s : Set.Ioc (0 : NNReal) u, g s) =
      ∑' s : Set.Ioc (0 : NNReal) t, if (s : NNReal) ≤ u then g s else 0 := by
  sorry
