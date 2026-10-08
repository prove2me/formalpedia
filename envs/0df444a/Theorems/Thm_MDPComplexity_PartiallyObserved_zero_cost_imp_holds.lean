-- Prove2me | Theorems.Thm_MDPComplexity_PartiallyObserved_zero_cost_imp_holds
-- name    : MDPComplexity.PartiallyObserved.zero_cost_imp_holds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:02:51.87424+00:00
-- url     : https://prove2.me/theorems/06fe21a4-2b0b-4f89-bb9e-18f8b285ae2e
-- title:
--   §4, proof of Theorem 6 (p. 449) — a zero-cost policy makes the formula true
-- statement:
--   Let $\varphi$ be a QSAT formula of the paper's alternating, three-literal form with $n$ variables and $m \ge 1$ clauses, and $M_\varphi$ the partially observed process of the proof of Theorem 6 with horizon $T = 2n+2$. If some observation-history policy $\pi$ satisfies
--   $$
--   J_\pi(T) = 0,
--   $$
--   then $\varphi$ is true.
--
--   This is the "only if" direction of the reduction: the policy's choices at the sets of existential variables, based on the observations made at the sets of earlier universal variables, give a winning strategy for the existential player that satisfies every clause.
--
--   **Formalization Note.** The policy sees only the sequence of sets of the partition, never the state, and in particular never the chosen clause. The paper's remark that the process runs "without ever observing the real value of $i$" is not literal under its own partition ($T_j$ and $T'_j$ are distinct sets), but the claim does not depend on it. The horizon is $2n+2$, corrected from the printed $2m+2$.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 449, proof of Theorem 6

import Mathlib
import Definitions.Def_MDPComplexity_PartiallyObserved_Construction

namespace MDPComplexity.PartiallyObserved

/-- §4, proof of Theorem 6 (p. 449), "only if": if some observation-history policy has expected
cost zero over the horizon `2n + 2`, the quantified formula is true. -/
theorem zero_cost_imp_holds {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (hqsat : φ.IsPaperQSAT)
    (π : (φ.toPOMDP hm).Policy)
    (h0 : (φ.toPOMDP hm).expCost .s0 π (horizon n) = 0) :
    φ.holds := by sorry

end MDPComplexity.PartiallyObserved
