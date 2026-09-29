-- Prove2me | Theorems.Thm_Hirsch_plane_bound_general
-- name    : Hirsch.plane_bound_general
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T08:43:36.843315+00:00
-- url     : https://prove2.me/theorems/3456238b-5a65-42cf-85c5-273887a2db27
-- title:
--   Hirsch in the plane, for unbounded polyhedra too
-- statement:
--   Let $P=\{x\in\mathbb{R}^2:\langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ with every $a_i\ne 0$. Then the combinatorial diameter of the vertex-edge graph of $P$ is at most $n-2$:
--
--   $$\Delta(2,n)\ \le\ n-2 .$$
--
--   This is the Hirsch bound in dimension two, and it is stated here for an arbitrary plane H-polyhedron — the polyhedron need not be bounded, and need not be nonempty. For bounded polygons the bound follows from Euler-type counting; the general statement is what a diameter induction on dimension needs, because the polyhedra such an induction produces (by deleting inequalities, or by passing to a facet) are unbounded in general.
--
--   The proof counts inequalities along a shortest walk. Each edge of the walk carries an inequality tight at both its endpoints — unless the polyhedron is that single edge, which a walk of length at least two rules out — and two distinct edges cannot carry the same inequality, because in the plane a single inequality is tight at no more than two vertices. The two endpoints of the walk each contribute one further inequality, distinct from all of these and from one another: two vertices sharing a tight inequality are adjacent in the plane, so the endpoints of a shortest walk of length at least two have disjoint tight sets. A walk of length $L$ therefore forces $L+2\le n$.
-- source:
--   V. Klee and P. Kleinschmidt, The d-step conjecture and its relatives, Math. Oper. Res. 12 (1987), 718-755, section 2 (the case d = 2); M. J. Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, https://arxiv.org/abs/1402.3579, p. 2 (the base cases of the induction)

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem plane_bound_general (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 2)) (b : Fin n → ℝ)
    (hane : ∀ i, a i ≠ 0) : DiamLE (Hpoly a b) (n - 2) := by sorry

end Hirsch
