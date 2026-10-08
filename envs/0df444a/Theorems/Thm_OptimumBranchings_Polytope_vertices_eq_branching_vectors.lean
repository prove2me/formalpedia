-- Prove2me | Theorems.Thm_OptimumBranchings_Polytope_vertices_eq_branching_vectors
-- name    : OptimumBranchings.Polytope.vertices_eq_branching_vectors
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:56:28.544989+00:00
-- url     : https://prove2.me/theorems/aa5153c0-a0c3-4e99-a805-cbf1f116df2f
-- title:
--   Theorem 2 — the vertices of $P_G$ are precisely the branching vectors
-- statement:
--   Let $G$ be a directed graph: finitely many nodes and edges, each edge directed from a rear end to a different front end, parallel edges allowed. Let $P_G\subseteq\mathbb R^E$ be the polyhedron defined by $(L_1)$ $x_e\ge0$, $(L_2)$ $\sum_{e\text{ into }v}x_e\le1$ for every node $v$, and $(L_3)$ $\sum_{e\text{ with both ends in }S}x_e\le|S|-1$ for every set $S$ of two or more nodes. Then
--   $$
--   \{x : x\text{ is a vertex of }P_G\}=\{x^B : B\text{ is a branching of }G\},
--   $$
--   where $x^B$ is the incidence vector of $B$ and a vertex is a point of $P_G$ that is the unique maximizer over $P_G$ of some linear function.
--
--   This is Edmonds' description of the branching polytope: the linear system $(L_1)$–$(L_3)$ has no fractional vertices, so optimum branchings can be found by linear programming and certified by duality.
--
--   **Formalization Note** The graph carries an explicit no-loop condition, as in the paper's definition; with a loop the theorem would be false.
-- source:
--   Edmonds, Optimum branchings, J. Res. Nat. Bur. Standards 71B (1967), p. 235, Theorem 2

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph
import Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron

namespace OptimumBranchings.Polytope

/-- Edmonds (1967), Theorem 2, p. 235: the vertices of the polyhedron `P_G` are precisely the
vectors of the subsets of edges in `G` which comprise branchings. -/
theorem vertices_eq_branching_vectors {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) :
    {x : E → ℝ | IsVertex (branchingPolyhedron G) x} =
      {x : E → ℝ | ∃ B : Finset E, G.IsBranching B ∧ x = incidenceVector B} := by sorry

end OptimumBranchings.Polytope
