-- Prove2me | Theorems.Thm_OptimumBranchings_Polytope_exists_branching_dual_certificate
-- name    : OptimumBranchings.Polytope.exists_branching_dual_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:55:28.039988+00:00
-- url     : https://prove2.me/theorems/0761a74e-c8b1-44cf-ad23-1342916e9492
-- title:
--   §7, p. 237 — for any weights there is a branching with a dual certificate (15)–(20)
-- statement:
--   Let $G$ be a directed graph (finite, parallel edges allowed, no loops) and let $c=(c_e)$ be arbitrary real edge weights. Then there exist a branching $B$ of $G$ and a dual vector $y=(y_h,y_S)$ — one number per node and one per set of two or more nodes — which together with the incidence vector of $B$ satisfy conditions (15)–(20).
--
--   In the paper the branching is the output of the shrinking algorithm of §4 and the vector $y$ is built along the unwinding of that algorithm; this statement records exactly the existence that Lemma 1 needs, without reference to the algorithm.
-- source:
--   Edmonds, Optimum branchings, J. Res. Nat. Bur. Standards 71B (1967), pp. 237–238, Section 7

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph
import Definitions.Def_OptimumBranchings_Polytope_BranchingPolyhedron
import Definitions.Def_OptimumBranchings_Polytope_DualCertificate

namespace OptimumBranchings.Polytope

/-- Edmonds (1967), §7, pp. 237–238 (algorithm-free form): for every choice of real edge weights
`c` there are a branching `B` and a vector `y = [yNode, ySet]` satisfying (15)–(20) for `c` and
the vector of `B`. (In the paper, `B` is the output of the algorithm of §4.) -/
theorem exists_branching_dual_certificate {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) (c : E → ℝ) :
    ∃ (B : Finset E) (yNode : V → ℝ) (ySet : Finset V → ℝ),
      G.IsBranching B ∧ IsDualCertificate G c B yNode ySet := by sorry

end OptimumBranchings.Polytope
