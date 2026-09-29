-- Prove2me | Theorems.Thm_OptimumBranchings_Polytope_lemma_1
-- name    : OptimumBranchings.Polytope.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:55:52.227989+00:00
-- url     : https://prove2.me/theorems/5306355f-0d06-4da8-94fa-931c9eb6f4b9
-- title:
--   Lemma 1 — every linear function is maximized over $P_G$ by a branching vector
-- statement:
--   Let $G$ be a directed graph (finite, parallel edges allowed, no loops) and let $c=(c_e)$ be arbitrary real edge weights. Then there is a branching $B$ of $G$ whose incidence vector $x^B$ lies in $P_G$ and maximizes the linear function $\sum_e c_e x_e$ over $P_G$:
--   $$
--   x^B\in P_G\quad\text{and}\quad\sum_e c_e x_e\le\sum_e c_e x^B_e\ \ \text{for all }x\in P_G .
--   $$
--
--   Together with the definition of a vertex this gives the inclusion "vertices $\subseteq$ branching vectors" of Theorem 2, and it shows that the optimum branching problem is solved by the linear program over $P_G$.
-- source:
--   Edmonds, Optimum branchings, J. Res. Nat. Bur. Standards 71B (1967), p. 236, Lemma 1

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph
import Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron

namespace OptimumBranchings.Polytope

/-- Edmonds (1967), Lemma 1, p. 236: every linear function `∑ c_e x_e` is maximized in `P_G` by
the vector of some branching in `G`. -/
theorem lemma_1 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ) :
    ∃ B : Finset E, G.IsBranching B ∧ incidenceVector B ∈ branchingPolyhedron G ∧
      ∀ x ∈ branchingPolyhedron G, ∑ e, c e * x e ≤ ∑ e, c e * incidenceVector B e := by sorry

end OptimumBranchings.Polytope
