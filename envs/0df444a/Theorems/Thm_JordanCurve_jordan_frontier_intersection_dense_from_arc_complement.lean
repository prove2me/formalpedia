-- Prove2me | Theorems.Thm_JordanCurve_jordan_frontier_intersection_dense_from_arc_complement
-- name    : JordanCurve.jordan_frontier_intersection_dense_from_arc_complement
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T00:36:38.775743+00:00
-- url     : https://prove2.me/theorems/491479e2-51ae-441e-918a-156d0dbd0df5
-- title:
--   Dense two-sided frontier for a Jordan curve
-- statement:
--   Assuming every simple planar arc has connected complement, let two disjoint open connected sets partition the complement of an embedded circle. Every point of the curve lies in the closure of the intersection of their frontiers.
-- source:
--   https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Topology

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

namespace JordanCurve

/-- The intersection of the two region frontiers is dense along a Jordan curve.
This is the local accessibility step in the arc-complement approach. -/
theorem jordan_frontier_intersection_dense_from_arc_complement
    (hArc : ∀ α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
      Continuous α → Function.Injective α →
        IsConnected ((Set.range α)ᶜ))
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ)
    (inside outside : Set (EuclideanSpace ℝ (Fin 2)))
    (hiopen : IsOpen inside) (hoopen : IsOpen outside)
    (hiconn : IsConnected inside) (hoconn : IsConnected outside)
    (hdisj : Disjoint inside outside)
    (hcover : inside ∪ outside = (Set.range γ)ᶜ) :
    Set.range γ ⊆ closure (frontier inside ∩ frontier outside) := by sorry

end JordanCurve
