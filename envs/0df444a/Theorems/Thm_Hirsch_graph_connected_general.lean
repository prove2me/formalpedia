-- Prove2me | Theorems.Thm_Hirsch_graph_connected_general
-- name    : Hirsch.graph_connected_general
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T08:13:40.560954+00:00
-- url     : https://prove2.me/theorems/af683513-c4df-42b6-a6f5-16a964ceba42
-- title:
--   The vertex-edge graph of an H-polyhedron is connected
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ be an H-polyhedron, not assumed bounded. Then any two vertices of $P$ are joined by a walk in its vertex-edge graph: the graph of a polyhedron is connected.
--
--   For bounded polytopes this is classical and follows from the simplex descent inside the convex hull of the vertices. For unbounded polyhedra the convex-hull description is unavailable, and the standard route is to cut the polyhedron with an auxiliary inequality. Taking the cut $\langle-\sum_i a_i,x\rangle\le M$ bounds every $\langle a_j,x\rangle$ from below as well as above, so the truncation is a bounded polytope as soon as the normals span, which they do whenever $P$ has a vertex. Perturbing the functional that exposes the target vertex by a small multiple of the cut functional makes every vertex created by the cut strictly worse than every vertex of $P$; a descending walk in the truncation therefore never meets one, and each of its edges is an edge of $P$ because on the line through two vertices the polyhedron is exactly the segment between them.
--
--   Connectivity of the graph is the hypothesis under which the Kalai--Kleitman diameter recursion is usually stated; making it a theorem for unbounded polyhedra is what allows that recursion to be applied to the relaxations it produces, which are unbounded in general.
-- source:
--   M. J. Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, https://arxiv.org/abs/1402.3579, p. 1 (definitions of vertex, edge and path in a polyhedron); G. M. Ziegler, Lectures on Polytopes, GTM 152, Springer 1995, Chapter 3 (graphs of polytopes)

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem graph_connected_general (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b)) :
    ∃ L, ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w L = v ∧
      ∀ j < L, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry

end Hirsch
