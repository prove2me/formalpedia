-- Prove2me | Theorems.Thm_JordanCurve_two_components_from_arc_complement
-- name    : JordanCurve.two_components_from_arc_complement
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T00:29:21.126019+00:00
-- url     : https://prove2.me/theorems/df3e625b-5091-4593-92fe-1c0dabf6d20c
-- title:
--   Jordan component counting from arc non-separation
-- statement:
--   Assume that every continuous injective image of a closed interval has connected complement in the plane. Then any continuous injective image $J$ of the circle has exactly two complementary connected components, one bounded and one unbounded. In the formal statement the two components are identified by points $a,b\notin J$, their disjointness and union cover, and their boundedness properties. This isolates the deduction of Jordan separation from simple-arc non-separation.
-- source:
--   Jordan proof through arc-complement non-separation, Schoenflies/JordanClosed.lean, https://github.com/alonamaloh/schoenflies-lean/blob/main/Schoenflies/JordanClosed.lean.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

namespace JordanCurve
theorem two_components_from_arc_complement
    (hArc : ∀ α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
      Continuous α → Function.Injective α →
        IsConnected ((Set.range α)ᶜ))
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ a b : EuclideanSpace ℝ (Fin 2),
      a ∉ Set.range γ ∧ b ∉ Set.range γ ∧
      Disjoint
        (connectedComponentIn ((Set.range γ)ᶜ) a)
        (connectedComponentIn ((Set.range γ)ᶜ) b) ∧
      connectedComponentIn ((Set.range γ)ᶜ) a ∪
        connectedComponentIn ((Set.range γ)ᶜ) b = (Set.range γ)ᶜ ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) ∧
      ¬ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) b) := by sorry
end JordanCurve
