-- Prove2me | Theorems.Thm_MechanismDesign_Robust_compromise_equity_dominates
-- name    : MechanismDesign.Robust.compromise_equity_dominates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:21:22.118995+00:00
-- url     : https://prove2.me/theorems/a0e21bc7-0da3-4d24-a355-f6ddb2e29f69
-- title:
--   Proposition 10.15 -- random dictatorship with compromise ex post equity dominates random dictatorship
-- statement:
--   In the voting environment of §10.11, for every $p \in [0,1]$, $p$-random dictatorship with compromise has a Bayesian equilibrium in truthful strategies (every acceptable set contains the agent's most preferred candidate and every reported ranking is her true preference) on the space $\mathcal T^+$ of all finite types that ex post equity dominates $p$-random dictatorship: its expected ex post equity is at least as large at every type profile and strictly larger at some.
--
--   A designer who values compromise for its own sake prefers the compromise mechanism, even though no mechanism ex post Pareto dominates random dictatorship.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.200, Proposition 10.15, Definition 10.21

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Voting

open scoped ENNReal NNReal

namespace MechanismDesign.Robust

/-- Proposition 10.15 (Börgers p.200). In the voting environment of §10.11, for every
`p ∈ [0, 1]`, `p`-random dictatorship with compromise has a Bayesian equilibrium in truthful
strategies on the space `T⁺` of all finite types that ex post equity dominates `p`-random
dictatorship. -/
theorem compromise_equity_dominates {Θ : Fin 2 → Type} [∀ i, Nonempty (Θ i)]
    (vu : ∀ i, Θ i → Candidate → ℝ) (henv : IsVotingEnvironment vu)
    (p : ℝ≥0) (hp : p ≤ 1) :
    ∃ σ : ∀ i, TPlusType Θ i → PMF CompromiseStrategy,
      IsTruthfulProfile (TPlus Θ) vu σ ∧
      IsBayesEq (TPlus Θ) (votingUtility vu) (compromiseMechanism p hp) σ ∧
      Dominates (equityWelfare (TPlus Θ) vu (compromiseMechanism p hp) σ)
        (equityWelfare (TPlus Θ) vu (rdMechanism p hp) (rdStrategy (TPlus Θ) vu)) := by sorry

end MechanismDesign.Robust
