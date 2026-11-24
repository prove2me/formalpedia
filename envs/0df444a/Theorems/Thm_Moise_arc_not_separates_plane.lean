-- Prove2me | Theorems.Thm_Moise_arc_not_separates_plane
-- name    : Moise.arc_not_separates_plane
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T21:23:31.752118+00:00
-- url     : https://prove2.me/theorems/9be052ad-551b-408d-b568-f088bb6e5839
-- title:
--   An arc does not separate $\mathbb{R}^2$
-- statement:
--   Let $\alpha : [0,1] \to \mathbb{R}^2$ be a continuous injective map (a topological arc). Then its complement $\mathbb{R}^2 \setminus \alpha([0,1])$ is connected.
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 4.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic

namespace Moise

theorem arc_not_separates_plane (α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (hα : Continuous α) (hinj : Function.Injective α) :
    _root_.IsConnected (Set.range α)ᶜ := by sorry

end Moise
