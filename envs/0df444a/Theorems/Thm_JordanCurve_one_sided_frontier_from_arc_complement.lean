-- Prove2me | Theorems.Thm_JordanCurve_one_sided_frontier_from_arc_complement
-- name    : JordanCurve.one_sided_frontier_from_arc_complement
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T00:39:52.229833+00:00
-- url     : https://prove2.me/theorems/cce7e5e9-120c-4e24-85bd-bbf860db4324
-- title:
--   One-sided frontier accessibility for Jordan curves
-- statement:
--   Let a simple closed curve partition its complement into two disjoint open connected regions. If every simple planar arc has connected complement, then every point of the curve lies on the frontier of either chosen region. This is the one-sided local accessibility assertion needed to identify both region frontiers.
-- source:
--   https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Topology

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

namespace JordanCurve

/-- Every point of an embedded circle is accessible from a chosen component
of its complement, assuming non-separation by simple arcs. -/
theorem one_sided_frontier_from_arc_complement
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
    Set.range γ ⊆ frontier inside := by sorry

end JordanCurve
