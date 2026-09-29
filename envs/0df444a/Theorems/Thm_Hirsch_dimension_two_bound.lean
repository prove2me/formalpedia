-- Prove2me | Theorems.Thm_Hirsch_dimension_two_bound
-- name    : Hirsch.dimension_two_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T02:05:48.929683+00:00
-- url     : https://prove2.me/theorems/803cd038-2ef1-43f2-ab89-655535741586
-- title:
--   The Hirsch bound in the plane: $\\mathrm{diam} \\le n-2$
-- statement:
--   **The Hirsch bound in ambient dimension two.** Every nonempty bounded H-polytope $P = \{x \in \mathbb{R}^2 \mid \langle a_i, x\rangle \le b_i,\ i < n\}$ has combinatorial diameter at most $n - 2$: any two vertices of $P$ are joined by a walk of at most $n-2$ steps in its vertex-edge graph.
--
--   This is the planar case of the Hirsch bound. A bounded $2$-dimensional H-polytope with $m$ vertices is a convex $m$-gon, whose vertex-edge graph is the $m$-cycle $C_m$ and therefore has diameter exactly $\lfloor m/2 \rfloor$. Each of the $m$ edges lies on a distinct facet, so $m \le n$, and $\lfloor m/2 \rfloor \le n - 2$ holds for every $m \ge 3$; the degenerate cases $m \le 2$ (a point or a segment) are covered separately, boundedness forcing $n \ge 3$ there. Lower-dimensional polytopes sitting inside $\mathbb{R}^2$ are included, and $n$ counts the inequalities of the given description (at least the number of facets), the subtraction being truncated natural subtraction.
--
--   Together with the elementary cases $d \le 1$ and the three-dimensional case this yields the mission's milestone `Hirsch.dimension_three_bound`.
-- source:
--   Klee, Diameters of polyhedral graphs, Canad. J. Math. 16 (1964) 602-614; Klee and Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967) 53-78, https://doi.org/10.1007/BF02392971. Stated here in the weakened form n - d used by the mission's milestone `Hirsch.dimension_three_bound`.

import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem dimension_two_bound (n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin 2)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - 2) := by sorry

end Hirsch
