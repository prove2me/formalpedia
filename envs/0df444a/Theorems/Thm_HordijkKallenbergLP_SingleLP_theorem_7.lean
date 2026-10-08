-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_theorem_7
-- name    : HordijkKallenbergLP.SingleLP.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:06:43.556735+00:00
-- url     : https://prove2.me/theorems/8037fa31-d46f-490a-8234-4dd92947724f
-- title:
--   Theorem 7 — a pure policy read off an extreme optimal solution of the dual LP is average optimal
-- statement:
--   Let $\beta_j>0$, $j\in E$, with $\sum_j\beta_j=1$, and let $(x,y)$ be an optimal solution of the dual program
--   $$\max\sum_i\sum_a r_{ia}x_{ia}\ \text{ s.t. }\ \sum_i\sum_a(\delta_{ij}-p_{iaj})x_{ia}=0,\ \ \sum_ax_{ja}+\sum_i\sum_a(\delta_{ij}-p_{iaj})y_{ia}=\beta_j,\ \ x,y\ge0,$$
--   obtained by the simplex method, i.e. an optimal solution that is an extreme point of the feasible set. Let $f$ be any decision rule with $f(i)=a_i\in A(i)$ such that
--   $$x_{ia_i}>0\ \ (i\in E_x=\{i\mid \textstyle\sum_a x_{ia}>0\}),\qquad y_{ia_i}>0\ \ (i\notin E_x).$$
--   Then $f^\infty$ is average optimal: $\varphi_i(f^\infty)=\sup_R\varphi_i(R)$ for every $i\in E$.
--
--   One linear program thus yields an average optimal pure stationary policy in every finite Markov decision chain, with no unichain assumption.
--
--   **Formalization Note** "The simplex method is used" is encoded as extremality of $(x,y)$ in the feasible set, the property of a basic feasible solution that the proof uses. The conclusion is asserted for every $f$ obeying the rule. Policies $R$ range over all history-dependent randomized policies.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, Theorem 7

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 7.** If the simplex method is used to solve the dual problem (3)–(5) and an optimal
solution `(x, y)` is obtained, then the policy `f^∞`, where `f(i) = a_i` such that `x_{i a_i} > 0`
for `i ∈ E_x = {i | Σ_a x_{ia} > 0}` and `y_{i a_i} > 0` for `i ∉ E_x`, is average optimal.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, Theorem 7.

**Formalization Note.** "The simplex method is used and an optimal solution is obtained" is
encoded as: `(x, y)` is an optimal solution of the dual program that is an extreme point of its
feasible set (a basic feasible solution, which is what the simplex method returns; the paper's
proof of Proposition 3 uses exactly this). Without extremality the statement is a different,
unproved claim. The conclusion holds for *every* `f` obeying the rule (Remark after Theorem 7:
"an arbitrary action"). Average optimality is Hordijk and Kallenberg's: `φ_i(f^∞) = φ_i` for all
`i`, against all history-dependent randomized policies. -/
theorem theorem_7 (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    IsAvgOptimal M (stationaryPolicy M f hf) := by sorry

end HordijkKallenbergLP.SingleLP
