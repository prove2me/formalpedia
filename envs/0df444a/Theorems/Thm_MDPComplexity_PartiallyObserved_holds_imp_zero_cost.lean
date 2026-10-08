-- Prove2me | Theorems.Thm_MDPComplexity_PartiallyObserved_holds_imp_zero_cost
-- name    : MDPComplexity.PartiallyObserved.holds_imp_zero_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:02:39.506987+00:00
-- url     : https://prove2.me/theorems/2df7681d-c190-4782-9eed-01cbaea0a787
-- title:
--   §4, proof of Theorem 6 (p. 449) — a true formula yields a zero-cost policy
-- statement:
--   Let $\varphi$ be a QSAT formula of the paper's alternating, three-literal form with $n$ variables and $m \ge 1$ clauses, and $M_\varphi$ the partially observed process of the proof of Theorem 6 with horizon $T = 2n+2$. If $\varphi$ is true, there is an observation-history policy $\pi$ with
--   $$
--   J_\pi(T) = 0.
--   $$
--
--   This is the "if" direction of the reduction: a strategy setting each existential variable from the values of the earlier universal ones translates into decisions at the sets of existential variables under which every clause reaches $A_{i,n+1}$.
--
--   **Formalization Note.** Policies map sequences of observations to decisions; the horizon is $2n+2$, corrected from the printed $2m+2$.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 449, proof of Theorem 6

import Mathlib
import Definitions.Def_MDPComplexity_PartiallyObserved_Construction

namespace MDPComplexity.PartiallyObserved

/-- §4, proof of Theorem 6 (p. 449), "if": if the quantified formula is true, some
observation-history policy has expected cost zero over the horizon `2n + 2`. -/
theorem holds_imp_zero_cost {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (hqsat : φ.IsPaperQSAT) (h : φ.holds) :
    ∃ π : (φ.toPOMDP hm).Policy, (φ.toPOMDP hm).expCost .s0 π (horizon n) = 0 := by sorry

end MDPComplexity.PartiallyObserved
