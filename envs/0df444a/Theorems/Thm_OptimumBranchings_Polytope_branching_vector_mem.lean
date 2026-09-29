-- Prove2me | Theorems.Thm_OptimumBranchings_Polytope_branching_vector_mem
-- name    : OptimumBranchings.Polytope.branching_vector_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:53:18.205999+00:00
-- url     : https://prove2.me/theorems/da249abc-806c-400a-98c0-660fd5f309b5
-- title:
--   §5, p. 236 — the vector of a branching is a point of $P_G$
-- statement:
--   Let $G$ be a directed graph (finite, parallel edges allowed, no loops) and let $B$ be a branching of $G$ with incidence vector $x^0$. Then
--   $$
--   x^0\in P_G ,
--   $$
--   that is, $x^0$ satisfies $(L_1)$, $(L_2)$ and $(L_3)$.
--
--   This is the first half of the observation in §5 that branching vectors are vertices of $P_G$; it is also what lets the maximum of a linear function over $P_G$ be compared with its maximum over branchings.
-- source:
--   Edmonds, Optimum branchings, J. Res. Nat. Bur. Standards 71B (1967), p. 236, Section 5

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph
import Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron

namespace OptimumBranchings.Polytope

/-- Edmonds (1967), §5, p. 236: the vector of a branching is a point of `P_G`. -/
theorem branching_vector_mem {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (B : Finset E) (hB : G.IsBranching B) :
    incidenceVector B ∈ branchingPolyhedron G := by sorry

end OptimumBranchings.Polytope
