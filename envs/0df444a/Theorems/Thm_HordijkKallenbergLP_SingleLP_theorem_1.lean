-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_theorem_1
-- name    : HordijkKallenbergLP.SingleLP.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:53:04.135391+00:00
-- url     : https://prove2.me/theorems/39746983-fcaa-4fe3-9c5e-8f111853b6c6
-- title:
--   Theorem 1 (Blackwell) — a pure stationary policy is α-discounted optimal for all α near 1
-- statement:
--   Consider a finite Markov decision chain with state space $E$, finite action sets $A(i)$, rewards $r_{ia}$ and transition probabilities $p_{iaj}$. There exists a pure and stationary policy $f_0^\infty$ and a number $\alpha_0\in[0,1)$ such that, for every discount factor $\alpha\in[\alpha_0,1)$,
--   $$v_i^\alpha(f_0^\infty)\ \ge\ v_i^\alpha(R)\qquad\text{for every policy }R\text{ and every }i\in E .$$
--
--   This is Blackwell's existence theorem for policies that are optimal for all discount factors near $1$; Theorems 4 and 5 are about such a policy.
--
--   **Formalization Note** The comparison runs over all history-dependent randomized policies.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, Theorem 1

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 1 (Blackwell).** There exists a pure and stationary policy `f₀^∞` such that `f₀^∞`
is α-discounted optimal for all α near enough to 1.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, Theorem 1.

**Formalization Note.** "α-discounted optimal" compares against every history-dependent
randomized policy (`AvgHRPolicy M`), as on p. 353; "for all α near enough to 1" is
`IsDiscOptimalNearOne` (some `α₀ ∈ [0, 1)` with optimality on `[α₀, 1)`). -/
theorem theorem_1 (M : StationaryMDP S A) [Nonempty S] :
    ∃ (f₀ : S → A) (hf₀ : ∀ i, f₀ i ∈ M.admissible i), IsDiscOptimalNearOne M f₀ hf₀ := by sorry

end HordijkKallenbergLP.SingleLP
