-- Prove2me | Theorems.Thm_Hirsch_klee_three_dimensional_bound
-- name    : Hirsch.klee_three_dimensional_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T02:06:09.935304+00:00
-- url     : https://prove2.me/theorems/27cbd6a5-fd56-4e8a-b240-ffffdf1f9ecc
-- title:
--   Klee's bound for $3$-polytopes: $\\mathrm{diam} \\le n-3$
-- statement:
--   **Klee's theorem in ambient dimension three.** Every nonempty bounded H-polytope $P = \{x \in \mathbb{R}^3 \mid \langle a_i, x\rangle \le b_i,\ i < n\}$ has combinatorial diameter at most $n - 3$.
--
--   Klee (1964) determined the exact maximum diameter of a $3$-polytope with $n$ facets, $\lfloor 2n/3 \rfloor - 1$, which is strictly below the Hirsch value $n-3$ for $n > 3$; the statement here is that exact result weakened to the Hirsch bound, which is all the mission's milestone needs. The proof is genuinely three-dimensional: it rests on the planar structure of the graph of a $3$-polytope (Steinitz) rather than on the facet-induction that drives the higher-dimensional bounds, which is why dimension three is the last dimension in which the Hirsch bound is known by an elementary argument.
--
--   As elsewhere in this mission, lower-dimensional polytopes sitting inside $\mathbb{R}^3$ are included, $n$ counts the inequalities of the given description (at least the number of facets), and the subtraction is truncated natural subtraction.
-- source:
--   Klee, Diameters of polyhedral graphs, Canad. J. Math. 16 (1964) 602-614; Klee and Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967) 53-78, https://doi.org/10.1007/BF02392971. Stated here in the weakened form n - d used by the mission's milestone `Hirsch.dimension_three_bound`.

import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem klee_three_dimensional_bound (n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin 3)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - 3) := by sorry

end Hirsch
