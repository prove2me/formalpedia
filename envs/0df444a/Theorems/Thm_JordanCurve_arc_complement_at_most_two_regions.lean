-- Prove2me | Theorems.Thm_JordanCurve_arc_complement_at_most_two_regions
-- name    : JordanCurve.arc_complement_at_most_two_regions
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T00:36:38.389011+00:00
-- url     : https://prove2.me/theorems/19932e9c-5154-45ad-8576-604e8d04ad22
-- title:
--   At most two Jordan complementary regions from arc non-separation
-- statement:
--   Assuming that every simple planar arc has connected complement, any two distinct complementary components of a Jordan curve cover the complement.
-- source:
--   https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Topology

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

namespace JordanCurve

/-- Under planar non-separation of simple arcs, two distinct components of a
Jordan complement exhaust that complement. -/
theorem arc_complement_at_most_two_regions
    (hArc : ∀ α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
      Continuous α → Function.Injective α →
        IsConnected ((Set.range α)ᶜ))
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ)
    (a b : EuclideanSpace ℝ (Fin 2))
    (ha : a ∉ Set.range γ) (hb : b ∉ Set.range γ)
    (hdisj : Disjoint
      (connectedComponentIn ((Set.range γ)ᶜ) a)
      (connectedComponentIn ((Set.range γ)ᶜ) b)) :
    connectedComponentIn ((Set.range γ)ᶜ) a ∪
      connectedComponentIn ((Set.range γ)ᶜ) b = (Set.range γ)ᶜ := by sorry

end JordanCurve
