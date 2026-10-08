-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_theorem_7_well_defined
-- name    : HordijkKallenbergLP.SingleLP.theorem_7_well_defined
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:59:12.074204+00:00
-- url     : https://prove2.me/theorems/e9645e31-8cf3-4c3f-aa82-4d6515e73112
-- title:
--   Proof of Theorem 7 (p. 357) — Σ_a x_ja + Σ_a y_ja ≥ β_j, so the policy f^∞ is well defined
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$, and let $(x,y)$ be a feasible solution of the dual program (3)–(5). Then
--   $$\sum_{a\in A(j)}x_{ja}+\sum_{a\in A(j)}y_{ja}\ \ge\ \beta_j\ >0,\qquad j\in E,$$
--   and hence the policy of Theorem 7 is well defined: there is a decision rule $f$ with $f(i)\in A(i)$ for all $i$, $x_{if(i)}>0$ for $i\in E_x$, and $y_{if(i)}>0$ for $i\notin E_x$.
--
--   This guarantees that the selection rule of Theorem 7 never gets stuck.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, §3.2, proof of Theorem 7

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proof of Theorem 7: the rule defines a policy.** For every feasible solution `(x, y)` of the
dual program (3)–(5), `Σ_a x_{ja} + Σ_a y_{ja} ≥ β_j > 0` for `j ∈ E`; hence the policy `f^∞` of
Theorem 7 is well defined: there is a decision rule `f` with `f(i) ∈ A(i)`, `x_{i f(i)} > 0` for
`i ∈ E_x` and `y_{i f(i)} > 0` for `i ∉ E_x`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, §3.2, proof of Theorem 7 (unnumbered). -/
theorem theorem_7_well_defined (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hz : z ∈ dualFeasible M β) :
    (∀ j : S, β j ≤ stateSum M z.1 j + stateSum M z.2 j) ∧
      ∃ (f : S → A) (hf : ∀ i, f i ∈ M.admissible i), IsSelection M z.1 z.2 f hf := by sorry

end HordijkKallenbergLP.SingleLP
