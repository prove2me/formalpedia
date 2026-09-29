-- Prove2me | Theorems.Thm_JordanCurve_simple_closed_curve_two_sided_accessibility
-- name    : JordanCurve.simple_closed_curve_two_sided_accessibility
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T00:15:57.794541+00:00
-- url     : https://prove2.me/theorems/3b7b653c-5e3a-46b6-a894-b65f85223077
-- title:
--   Every Jordan curve point borders both regions
-- statement:
--   Let $J$ be a continuous injective image of the unit circle. Suppose $U$ and $V$ are disjoint open connected sets whose union is the complement of $J$. Every point of the curve lies in both closures: $$J\subseteq\overline U\cap\overline V.$$ This is the local two-sidedness part of the Jordan curve theorem.
-- source:
--   Jordan curve theorem, common-boundary assertion; see A Proof of the Jordan Curve Theorem, https://doi.org/10.4236/ns.2019.1112037.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

namespace JordanCurve
theorem simple_closed_curve_two_sided_accessibility
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ)
    (inside outside : Set (EuclideanSpace ℝ (Fin 2)))
    (hiopen : IsOpen inside) (hoopen : IsOpen outside)
    (hiconn : IsConnected inside) (hoconn : IsConnected outside)
    (hdisj : Disjoint inside outside)
    (hcover : inside ∪ outside = (Set.range γ)ᶜ) :
    Set.range γ ⊆ closure inside ∩ closure outside := by sorry
end JordanCurve
