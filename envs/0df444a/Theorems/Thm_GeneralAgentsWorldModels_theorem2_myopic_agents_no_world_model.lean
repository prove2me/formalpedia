-- Prove2me | Theorems.Thm_GeneralAgentsWorldModels_theorem2_myopic_agents_no_world_model
-- name    : GeneralAgentsWorldModels.theorem2_myopic_agents_no_world_model
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:40:00.3298+00:00
-- url     : https://prove2.me/theorems/a90839de-bbe1-42fd-b9ae-5d3dcc41eb2b
-- title:
--   Theorem 2 (as proved): optimal myopic agents do not determine the transition probabilities
-- statement:
--   Let $S$ and $A$ be finite with $|S|\ge2$, and let the environment $P$ satisfy Assumption 1. Then there is an optimal myopic agent $\pi^*$ for $P$, that is, a goal-conditioned policy that is optimal for every goal in $\Psi_{\text{myopic}}$ (the depth-1 composite goals built from sub-goals $\medcirc[(s,a)\in g]$), with the following property: for every transition $(s,a,s')$ and every $q\in(0,1)$ there is an environment $P'$ satisfying Assumption 1 with $P'_{ss'}(a)=q$ for which $\pi^*$ is also an optimal myopic agent.
--
--   Thus the set of values of $P_{ss'}(a)$ compatible with the policy $\pi^*$ is dense in $[0,1]$, and any bound $|\hat P_{ss'}(a)-P_{ss'}(a)|\le\epsilon$ determined from $\pi^*$ alone is no better than the trivial one: learning a world model is not necessary for myopic agents.
--
--   **Formalization Note** The printed theorem speaks of any optimal myopic agent. That reading is false: an optimal agent may act arbitrarily at time $1$ after zero-probability transitions, and such behaviour can pin down a transition probability exactly (see the report). The proof constructs one agent from the argmax actions, which is why the statement given here is existential ('there is an optimal myopic agent'); the statement itself places no further constraint on $\pi^*$ (in the proof, the witness agent chooses its time-$1$ action inside the goal set whenever possible). The proof's witness environment has action-independent transitions; such an environment is not communicating when $s=s'$ and $q=1$ ($s$ is absorbing), or when $|S|=2$, $s\ne s'$ and $q=0$, so $q$ ranges over $(0,1)$, whose closure is $[0,1]$. With $|S|=1$ every transition probability equals $1$ and the printed theorem fails.
-- source:
--   Richens, Abel, Bellot and Everitt, General agents contain world models, arXiv:2506.01622v5 (ICML 2025), Section 3, Theorem 2, p. 5; proof in Appendix B, eq. (58), pp. 20-21

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

namespace GeneralAgentsWorldModels

theorem theorem2_myopic_agents_no_world_model {S A : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] (hS : 2 ≤ Fintype.card S) (M : CMP S A) (hM : SatisfiesAssumption1 M) :
    ∃ πstar : GCPolicy S A, IsOptimalAgent M PsiMyopic πstar ∧
      ∀ (s : S) (a : A) (s' : S) (q : ℝ), 0 < q → q < 1 →
        ∃ M' : CMP S A, SatisfiesAssumption1 M' ∧ M'.P s a s' = q ∧
          IsOptimalAgent M' PsiMyopic πstar := by sorry

end GeneralAgentsWorldModels
