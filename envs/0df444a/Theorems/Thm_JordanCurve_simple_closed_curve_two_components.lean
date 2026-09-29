-- Prove2me | Theorems.Thm_JordanCurve_simple_closed_curve_two_components
-- name    : JordanCurve.simple_closed_curve_two_components
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T00:23:20.390341+00:00
-- url     : https://prove2.me/theorems/3de6ef89-dd7a-474b-b7f8-924d798154b1
-- title:
--   Two connected components of a Jordan complement
-- statement:
--   Let $J$ be a continuous injective image of the unit circle in the plane. There are points $a,b$ off $J$ such that the connected components of $\mathbb R^2\setminus J$ containing $a$ and $b$ are disjoint, together cover the complement, and have different boundedness: the component of $a$ is bounded, while the component of $b$ is unbounded. This isolates the component-counting part of Jordan separation.
-- source:
--   Jordan curve theorem, separation step; cf. the independent Lean development Schoenflies/JordanClosed.lean, https://github.com/alonamaloh/schoenflies-lean/blob/main/Schoenflies/JordanClosed.lean.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

namespace JordanCurve
theorem simple_closed_curve_two_components
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
