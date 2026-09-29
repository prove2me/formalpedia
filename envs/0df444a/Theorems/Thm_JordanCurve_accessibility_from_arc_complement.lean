-- Prove2me | Theorems.Thm_JordanCurve_accessibility_from_arc_complement
-- name    : JordanCurve.accessibility_from_arc_complement
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T00:26:52.140283+00:00
-- url     : https://prove2.me/theorems/0ca6aac0-bde3-4fa8-9d75-39858e86ffe0
-- title:
--   Two-sided Jordan accessibility from arc non-separation
-- statement:
--   Assume the planar simple-arc non-separation theorem. For any simple closed curve $J$ whose complement is divided into two disjoint open connected regions $U,V$, every curve point can be approached from both regions: $$J\subseteq\overline U\cap\overline V.$$ This identifies the local topological deduction that follows the arc-complement result.
-- source:
--   Schoenflies/JordanClosed.lean, Jordan theorem derived from arc complement, https://github.com/alonamaloh/schoenflies-lean/blob/main/Schoenflies/JordanClosed.lean.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

namespace JordanCurve
theorem accessibility_from_arc_complement
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
    Set.range γ ⊆ closure inside ∩ closure outside := by sorry
end JordanCurve
