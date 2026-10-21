-- Prove2me | Theorems.Thm_InfoDesignGames_Existence_lift_selection
-- name    : InfoDesignGames.Existence.lift_selection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:25.811694+00:00
-- url     : https://prove2.me/theorems/8540a1d2-b8c4-4b5e-b2d4-904c3bfd6756
-- title:
--   Proof of Theorem 1, p. 7 — lift the selected payoffs to an agent-equilibrium selection
-- statement:
--   Suppose $U^*$ is a Borel measurable selection of the designer payoff correspondence $\mathcal U$, and $\zeta$ is a mixed Nash equilibrium of the designers' game with payoff $U^*$. Then there is a Borel measurable selection $\tau(x)\in E_M(x)$ for every $x$ that realizes exactly the same payoff vector and the same mixed Nash equilibrium:
--
--   $$\exists\tau,\quad U_i(x,\tau(x))=U_i^*(x)\ \forall x,i,\qquad \zeta\text{ is a mixed Nash equilibrium for }U^\tau.$$
--
--   This is the lift from a selected payoff profile to an actual continuation outcome in the agents' subgame.
--
--   **Formalization Note** The given $U^*$ and $\zeta$ are the objects produced in the preceding proof step, and $\tau$ is selected at every experiment profile, including profiles outside the support of $\zeta$.
-- source:
--   Koessler, Laclau & Tomala, Interactive Information Design, SSRN working paper 3171992 (version of April 25, 2018), https://ssrn.com/abstract=3171992, p. 7, final sentence of proof of Theorem 1

import Definitions.Def_InfoDesignGames_Existence_Model

namespace InfoDesignGames.Existence

theorem lift_selection (G : Game) (Ustar : Profile G → G.ι → ℝ)
    (hU : Measurable Ustar) (hsel : ∀ x, Ustar x ∈ payoffSet G x)
    (ζ : MixedProfile G) (hζ : IsMixedNashDesigners G Ustar ζ) :
    ∃ τ : Profile G → Outcome G,
      Measurable τ ∧ (∀ x, τ x ∈ EM G x) ∧
        (∀ x i, designerPayoff G i x (τ x) = Ustar x i) ∧
        IsMixedNashDesigners G (fun x i => designerPayoff G i x (τ x)) ζ := by sorry

end InfoDesignGames.Existence
