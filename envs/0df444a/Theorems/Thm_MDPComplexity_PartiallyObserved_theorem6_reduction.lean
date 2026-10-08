-- Prove2me | Theorems.Thm_MDPComplexity_PartiallyObserved_theorem6_reduction
-- name    : MDPComplexity.PartiallyObserved.theorem6_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:02:42.858813+00:00
-- url     : https://prove2.me/theorems/bcc5371a-7647-452b-a643-2af5412a7695
-- title:
--   Theorem 6, the reduction (pp. 448–449, horizon corrected to $2n+2$): a quantified formula is true iff its partially observed process has a zero-cost policy
-- statement:
--   Let $\varphi$ be a QSAT formula of the paper's alternating, three-literal form with $n$ variables and $m \ge 1$ clauses, let $M_\varphi$ be the partially observed stationary Markov decision process built from it in the proof of Theorem 6 (state set $S$, initial state $s_0$), and let $T = 2n + 2$. Then
--
--   1. $T < |S|$;
--   2. there exists an observation-history policy $\pi$ with expected cost $J_\pi(T) = 0$ if and only if $\varphi$ is true;
--   3. the optimal expected cost satisfies
--   $$
--   \inf_\pi J_\pi(T) \le 0 \iff \varphi \text{ is true}.
--   $$
--
--   This is the mathematical content of Theorem 6 of Papadimitriou and Tsitsiklis: since quantified satisfiability is PSPACE-complete and the construction is computable in polynomial time, deciding whether a partially observed stationary process with horizon $T < |S|$ achieves cost $0$ is PSPACE-hard.
--
--   **Formalization Note.** The paper prints the horizon as $2m+2$ ("just enough time for the process to reach one of $A_{i,n+1}$ or $A'_{i,n+1}$"); that time is $2n+1$, so we use $T = 2n+2$, which keeps $T < |S| = 6mn + 2m + 2$. `IsPaperQSAT` enforces the alternating prefix and three literals per clause; clauses are sets, with three witnesses allowing repeated literals. PSPACE-hardness itself, the polynomial-time computability of the construction, membership in PSPACE and Corollaries 1 and 2 are not formalized. The infimum is over all policies mapping observation sequences to decisions.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), pp. 448–449, Theorem 6 and its proof (horizon corrected from 2m + 2 to 2n + 2)

import Mathlib
import Definitions.Def_MDPComplexity_PartiallyObserved_Construction

namespace MDPComplexity.PartiallyObserved

/-- Theorem 6, the reduction (pp. 448–449), horizon corrected to `2n + 2`: for a quantified
formula with `m ≥ 1` clauses, the constructed partially observed stationary process has
`T < |S|`, a policy of expected cost zero exists iff the formula is true, and the optimal
expected cost is at most 0 iff the formula is true. -/
theorem theorem6_reduction {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (hqsat : φ.IsPaperQSAT) :
    horizon n < Fintype.card (St n m) ∧
    ((∃ π : (φ.toPOMDP hm).Policy, (φ.toPOMDP hm).expCost .s0 π (horizon n) = 0) ↔ φ.holds) ∧
    ((φ.toPOMDP hm).optCost .s0 (horizon n) ≤ 0 ↔ φ.holds) := by sorry

end MDPComplexity.PartiallyObserved
