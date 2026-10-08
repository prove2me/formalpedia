-- Prove2me | Theorems.Thm_MechanismDesign_Robust_compromise_interim_pareto_dominates
-- name    : MechanismDesign.Robust.compromise_interim_pareto_dominates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:21:14.637823+00:00
-- url     : https://prove2.me/theorems/9f13e2f9-1dfa-42f4-a29c-09d2aa7c5d92
-- title:
--   Proposition 10.13 -- random dictatorship with compromise interim Pareto dominates random dictatorship
-- statement:
--   In the voting environment of §10.11, for every $p \in (0,1)$, $p$-random dictatorship with compromise has a Bayesian equilibrium on the space $\mathcal T^+$ of all finite types that
--
--   1. interim Pareto dominates $p$-random dictatorship (with its equilibrium in which every type names her most preferred candidate): every type's interim expected utility is at least as large, and at some type profile some type's is strictly larger; and
--   2. satisfies positive and negative unanimity.
--
--   Dropping belief independence from Hylland's theorem, but not unanimity, permits improvements over random dictatorship.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.199, Proposition 10.13

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Voting

open scoped ENNReal NNReal

namespace MechanismDesign.Robust

/-- Proposition 10.13 (Börgers p.199). In the voting environment of §10.11, for every
`p ∈ (0, 1)`, `p`-random dictatorship with compromise has a Bayesian equilibrium on the space `T⁺`
of all finite types that interim Pareto dominates `p`-random dictatorship (Definition 10.19, with
its equilibrium) and satisfies positive and negative unanimity. -/
theorem compromise_interim_pareto_dominates {Θ : Fin 2 → Type} [∀ i, Nonempty (Θ i)]
    (vu : ∀ i, Θ i → Candidate → ℝ) (henv : IsVotingEnvironment vu)
    (p : ℝ≥0) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ σ : ∀ i, TPlusType Θ i → PMF CompromiseStrategy,
      IsBayesEq (TPlus Θ) (votingUtility vu) (compromiseMechanism p hp1.le) σ ∧
      Dominates (interimWelfare (TPlus Θ) (votingUtility vu) (compromiseMechanism p hp1.le) σ)
        (interimWelfare (TPlus Θ) (votingUtility vu) (rdMechanism p hp1.le)
          (rdStrategy (TPlus Θ) vu)) ∧
      PositiveUnanimity (TPlus Θ) vu (compromiseMechanism p hp1.le) σ ∧
      NegativeUnanimity (TPlus Θ) vu (compromiseMechanism p hp1.le) σ := by sorry

end MechanismDesign.Robust
