-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_theorem_4
-- name    : HordijkKallenbergLP.SingleLP.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:54:58.098372+00:00
-- url     : https://prove2.me/theorems/4d8e499b-6209-4859-af4b-80bbb4f66fda
-- title:
--   Theorem 4 (Derman) — the policy of Theorem 1 is average optimal
-- statement:
--   Let $f_0^\infty$ be a pure stationary policy that is α-discounted optimal for all α near enough to $1$ (the policy of Theorem 1). Then $f_0^\infty$ is average optimal:
--   $$\varphi_i(f_0^\infty)=\varphi_i=\sup_R\varphi_i(R),\qquad i\in E ,$$
--   the supremum running over all policies.
--
--   The theorem shows that average optimal pure stationary policies exist, and it identifies $\varphi$ with $\varphi(f_0^\infty)$ in the proof of Theorem 6.
--
--   **Formalization Note** The property of Theorem 1 is a hypothesis on $f_0$; Theorem 1 itself is not assumed. Average optimality is $\varphi(R^*)=\varphi$ with lim inf averages, as on p. 353.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, Theorem 4

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4 (Derman).** The policy `f₀^∞` from Theorem 1 is average optimal.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, Theorem 4.

**Formalization Note.** "The policy from Theorem 1" is the hypothesis that `f₀^∞` is α-discounted
optimal for all α near enough to 1 (`IsDiscOptimalNearOne`); Theorem 1 itself is not assumed.
Average optimality is Hordijk and Kallenberg's (`gainInf = optGainInf` at every state), not
Puterman's `IsAverageOptimal`. -/
theorem theorem_4 (M : StationaryMDP S A) [Nonempty S] (f₀ : S → A) (hf₀ : ∀ i, f₀ i ∈ M.admissible i)
    (h₀ : IsDiscOptimalNearOne M f₀ hf₀) :
    IsAvgOptimal M (stationaryPolicy M f₀ hf₀) := by sorry

end HordijkKallenbergLP.SingleLP
