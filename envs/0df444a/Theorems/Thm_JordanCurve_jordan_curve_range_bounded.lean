-- Prove2me | Theorems.Thm_JordanCurve_jordan_curve_range_bounded
-- name    : JordanCurve.jordan_curve_range_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T00:45:05.854071+00:00
-- url     : https://prove2.me/theorems/90cbea83-f423-4d50-9f13-97aa1a719e00
-- title:
--   Bounded image of a continuous Jordan parametrization
-- statement:
--   Let $\gamma:S^1\to\mathbb R^2$ be continuous. Its image is bounded: $$\exists R>0\;\forall z\in\gamma(S^1),\;\|z\|\le R.$$ This elementary compactness fact supports the construction of the unbounded complementary region.
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/MetricSpace/ProperSpace.lean

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded

namespace JordanCurve

/-- The continuous image of the unit circle in the plane is bounded. -/
theorem jordan_curve_range_bounded
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) :
    Bornology.IsBounded (Set.range γ) := by sorry

end JordanCurve
