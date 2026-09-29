-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_exists_lattice_point_near_halfLine
-- name    : MaxLatticeFree.Geometry.exists_lattice_point_near_halfLine
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:15:30.213656+00:00
-- url     : https://prove2.me/theorems/2846363f-2493-4cb9-91e6-d6d0b54e890d
-- title:
--   Lemma 15 — lattice points arbitrarily close to every half-line from a lattice point
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$. Let $y\in\Lambda$ and let $r\in V$ be a nonzero direction (not necessarily a lattice direction). Then for every $\varepsilon>0$ and every $\bar\lambda\ge0$ there is a point $z\in\Lambda$ with $z\neq y$ whose Euclidean distance to the half-line
--
--   $$
--   \{\,y+\lambda r \mid \lambda\ge\bar\lambda\,\}
--   $$
--
--   is less than $\varepsilon$.
--
--   This is a consequence of Dirichlet's simultaneous approximation theorem. It is the reason a maximal lattice-free set cannot have a recession direction that is not also a lineality direction (Lemma 16).
--
--   **Formalization Note** The distance from a point to the half-line is `Metric.infDist`; the half-line is nonempty, so no junk value arises.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 11, Lemma 15

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf

namespace MaxLatticeFree.Geometry

theorem exists_lattice_point_near_halfLine {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Λ) (r : EuclideanSpace ℝ (Fin n)) (hrV : r ∈ V) (hr0 : r ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ z ∈ Λ, z ≠ y ∧
      Metric.infDist z {p : EuclideanSpace ℝ (Fin n) | ∃ t : ℝ, lam ≤ t ∧ p = y + t • r} < ε := by sorry

end MaxLatticeFree.Geometry
