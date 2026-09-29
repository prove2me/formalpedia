-- Prove2me | Theorems.Thm_OptimumBranchings_Polytope_branching_vector_isVertex
-- name    : OptimumBranchings.Polytope.branching_vector_isVertex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:53:59.601985+00:00
-- url     : https://prove2.me/theorems/a3767ad2-2346-44b7-99ca-1f0cdff26e57
-- title:
--   §5, p. 236 — the vector of a branching is a vertex of $P_G$
-- statement:
--   Let $G$ be a directed graph (finite, parallel edges allowed, no loops) and let $B$ be a branching of $G$ with incidence vector $x^0$. Then $x^0$ is a vertex of $P_G$: $x^0\in P_G$ and there are real weights $c=(c_e)$ such that
--   $$
--   \sum_e c_e y_e<\sum_e c_e x^0_e\qquad\text{for every }y\in P_G,\ y\ne x^0 .
--   $$
--
--   This is the inclusion "branching vectors $\subseteq$ vertices" of Theorem 2.
-- source:
--   Edmonds, Optimum branchings, J. Res. Nat. Bur. Standards 71B (1967), p. 236, Section 5

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph
import Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron

namespace OptimumBranchings.Polytope

/-- Edmonds (1967), §5, p. 236: the vector of a branching is a vertex of `P_G`, i.e. the unique
maximizer over `P_G` of some linear function. -/
theorem branching_vector_isVertex {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (B : Finset E) (hB : G.IsBranching B) :
    IsVertex (branchingPolyhedron G) (incidenceVector B) := by sorry

end OptimumBranchings.Polytope
