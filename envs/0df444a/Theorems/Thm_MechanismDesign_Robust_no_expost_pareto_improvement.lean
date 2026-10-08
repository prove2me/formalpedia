-- Prove2me | Theorems.Thm_MechanismDesign_Robust_no_expost_pareto_improvement
-- name    : MechanismDesign.Robust.no_expost_pareto_improvement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:21:27.72784+00:00
-- url     : https://prove2.me/theorems/62d7827a-1527-4022-b045-c7b215443519
-- title:
--   Proposition 10.14 -- no mechanism ex post Pareto dominates random dictatorship
-- statement:
--   In the voting environment of §10.11, for every $p \in [0,1]$ there is no (finite) mechanism $M$ with a Bayesian equilibrium $\sigma^*$ on the space $\mathcal T^+$ of all finite types that ex post Pareto dominates $p$-random dictatorship; that is, there are no $M$, $\sigma^*$ under which at every type profile each agent's expected utility (at the true payoff types) is at least as large as under $p$-random dictatorship, and at some type profile some agent's is strictly larger.
--
--   **Formalization Note** Mechanisms range over finite mechanisms, the class §10.11 focuses on (p.195).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.199, Proposition 10.14

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Voting

open scoped ENNReal NNReal

namespace MechanismDesign.Robust

/-- Proposition 10.14 (Börgers p.199). In the voting environment of §10.11, for every
`p ∈ [0, 1]` there is no finite mechanism with a Bayesian equilibrium on the space `T⁺` of all
finite types that ex post Pareto dominates `p`-random dictatorship. -/
theorem no_expost_pareto_improvement {Θ : Fin 2 → Type} [∀ i, Nonempty (Θ i)]
    (vu : ∀ i, Θ i → Candidate → ℝ) (henv : IsVotingEnvironment vu)
    (p : ℝ≥0) (hp : p ≤ 1) :
    ¬ ∃ (S : Fin 2 → Type) (_ : ∀ i, Fintype (S i)) (M : Mechanism S Candidate)
        (σ : ∀ i, TPlusType Θ i → PMF (S i)),
        IsBayesEq (TPlus Θ) (votingUtility vu) M σ ∧
        Dominates (expostWelfare (TPlus Θ) (votingUtility vu) M σ)
          (expostWelfare (TPlus Θ) (votingUtility vu) (rdMechanism p hp)
            (rdStrategy (TPlus Θ) vu)) := by sorry

end MechanismDesign.Robust
