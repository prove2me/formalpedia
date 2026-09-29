-- Prove2me | Theorems.Thm_OptimumBranchings_Polytope_dual_certificate_optimal
-- name    : OptimumBranchings.Polytope.dual_certificate_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:54:58.623173+00:00
-- url     : https://prove2.me/theorems/0c888378-f051-4642-95d5-7e5524b99fe7
-- title:
--   §6, (12)–(14), p. 236 — a dual certificate (15)–(20) proves a branching optimal over $P_G$
-- statement:
--   Let $G$ be a directed graph (finite, parallel edges allowed, no loops) with real edge weights $c$, let $B$ be a branching with incidence vector $x^0$, and let $y=(y_h,y_S)$ satisfy conditions (15)–(20) for $c$ and $x^0$. Then
--
--   1. $(c,x^0)=(b,y)$, i.e. $\sum_e c_e x^0_e=\sum_h y_h+\sum_{|S|\ge2}(|S|-1)y_S$;
--   2. $x^0$ maximizes $(c,x)$ over $P_G$: $x^0\in P_G$ and
--   $$
--   \sum_e c_e x_e\le\sum_e c_e x^0_e\qquad\text{for all }x\in P_G ;
--   $$
--   3. $y$ minimizes $(b,y)$ over all dual feasible vectors, i.e. over all vectors satisfying (15)–(17).
--
--   This is the linear programming optimality criterion (weak duality plus complementary slackness) instantiated for the system $(L_1)$–$(L_3)$; it reduces the optimality of a branching over the whole polyhedron to the construction of a certificate.
-- source:
--   Edmonds, Optimum branchings, J. Res. Nat. Bur. Standards 71B (1967), p. 236, Section 6, (11)–(14), applied on p. 237 to (15)–(20)

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph
import Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron
import Definitions.Def_OptimumBranchings_Polytope_DualCertificate

namespace OptimumBranchings.Polytope

/-- Edmonds (1967), §6, (11)–(14) applied to (15)–(20), pp. 236–237: if `B` is a branching and
`(yNode, ySet)` satisfies (15)–(20) for the weights `c` and the vector `x⁰` of `B`, then
`(c, x⁰) = (b, y)`, `x⁰` maximizes `(c, x)` over `P_G`, and `y` minimizes `(b, y)` over all
vectors satisfying (15)–(17). -/
theorem dual_certificate_optimal {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (c : E → ℝ) (B : Finset E) (yNode : V → ℝ)
    (ySet : Finset V → ℝ) (hB : G.IsBranching B)
    (hy : IsDualCertificate G c B yNode ySet) :
    ∑ e, c e * incidenceVector B e = dualObjective yNode ySet ∧
    incidenceVector B ∈ branchingPolyhedron G ∧
    (∀ x ∈ branchingPolyhedron G, ∑ e, c e * x e ≤ ∑ e, c e * incidenceVector B e) ∧
    (∀ (zNode : V → ℝ) (zSet : Finset V → ℝ), IsDualFeasible G c zNode zSet →
      dualObjective yNode ySet ≤ dualObjective zNode zSet) := by sorry

end OptimumBranchings.Polytope
