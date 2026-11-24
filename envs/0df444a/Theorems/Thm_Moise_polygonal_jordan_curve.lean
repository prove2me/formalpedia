-- Prove2me | Theorems.Thm_Moise_polygonal_jordan_curve
-- name    : Moise.polygonal_jordan_curve
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T19:24:52.234806+00:00
-- url     : https://prove2.me/theorems/09eb0bab-13ff-4ded-b081-940f82db5638
-- title:
--   Jordan curve theorem for polygons
-- statement:
--   Let $P$ be a finite $1$-dimensional Euclidean complex in $\mathbb{R}^2$ whose polyhedron $|P|$ is homeomorphic to $S^1$ (a simple closed polygon). Then $\mathbb{R}^2 \setminus |P|$ is the disjoint union of two open connected sets $U$ (bounded) and $V$ (unbounded) whose common frontier is $|P|$:
--
--   $$\mathbb{R}^2 \setminus |P| = U \sqcup V, \qquad \partial U = \partial V = |P|.$$
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 2.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic
import Definitions.Def_Moise_EuclideanComplex

namespace Moise

theorem polygonal_jordan_curve (P : EuclideanComplex 2)
    (hfin : P.IsFinite) (hdim : ∀ σ ∈ P.simplices, σ.dim ≤ 1)
    (hS1 : Nonempty (P.polyhedron ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) :
    ∃ inside outside : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen inside ∧ IsOpen outside ∧
      IsConnected inside ∧ IsConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      Disjoint inside outside ∧
      inside ∪ outside = P.polyhedronᶜ ∧
      frontier inside = P.polyhedron ∧
      frontier outside = P.polyhedron := by sorry

end Moise
