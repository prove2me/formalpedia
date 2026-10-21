-- Prove2me | Theorems.Thm_InfoDesignGames_Existence_theorem_1
-- name    : InfoDesignGames.Existence.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:43.97699+00:00
-- url     : https://prove2.me/theorems/f7b3a965-879c-4069-b2db-82f3cf172961
-- title:
--   Theorem 1, p. 6 — existence of equilibrium in every finite-message information design game
-- statement:
--   For every finite information design game $G_M$, there are a Borel measurable continuation-outcome rule $\tau$ and an independent mixed-strategy profile $\zeta$ of the designers such that $\tau(x)$ is an agent Bayes Nash equilibrium outcome at **every** experiment profile $x$, and $\zeta$ is a mixed Nash equilibrium of the game with designer payoffs $U_i^\tau(x)=U_i(x,\tau(x))$:
--
--   $$\exists\tau,\zeta,\quad \tau(x)\in E_M(x)\ \forall x,\quad \tau\text{ is Borel measurable},\quad \zeta\text{ is a mixed Nash equilibrium for }U^\tau.$$
--
--   The selection at every $x$ supplies equilibrium behavior in every agents' continuation subgame, including those off the designers' equilibrium path.
--
--   **Formalization Note** The message sets are additionally required nonempty, since an empty message set would leave a designer without an experiment. $\tau$ is existential and must be measurable; the equilibrium predicate tests deviations to all Borel probability measures on the designers' experiment spaces.
-- source:
--   Koessler, Laclau & Tomala, Interactive Information Design, SSRN working paper 3171992 (version of April 25, 2018), https://ssrn.com/abstract=3171992, p. 6, Theorem 1 and Definition 2

import Definitions.Def_InfoDesignGames_Existence_Model

namespace InfoDesignGames.Existence

theorem theorem_1 (G : Game) :
    ∃ (τ : Profile G → Outcome G) (ζ : MixedProfile G),
      IsEquilibrium G τ ζ := by sorry

end InfoDesignGames.Existence
