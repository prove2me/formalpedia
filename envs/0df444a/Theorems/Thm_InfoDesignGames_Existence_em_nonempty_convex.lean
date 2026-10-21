-- Prove2me | Theorems.Thm_InfoDesignGames_Existence_em_nonempty_convex
-- name    : InfoDesignGames.Existence.em_nonempty_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:29.2553+00:00
-- url     : https://prove2.me/theorems/782a5bca-0136-48ba-aa57-9b88348130b9
-- title:
--   §2, p. 6 — nonempty convex agent equilibrium outcomes and public correlation
-- statement:
--   Fix a finite information design game $G_M$ and an experiment profile $x$. Let $E_M(x)$ be the outcome distributions induced by the agents' Bayes Nash equilibria when they share a uniform public signal. Then
--
--   $$E_M(x)\ne\varnothing,\qquad E_M(x)\text{ is convex},\qquad E_M(x)=\operatorname{conv}\{y_\sigma:\sigma\text{ is a device-free Bayes Nash equilibrium at }x\},$$
--
--   where $y_\sigma(a\mid m)$ is the product of the agents' action lotteries under $\sigma$. This identifies the public correlated equilibrium outcomes and supplies a nonempty continuation-outcome set at every subgame.
--
--   **Formalization Note** The model includes nonempty message sets in addition to the paper's nonempty state and action sets. The equality states the paper's coincidence clause through the convex hull of device-free Bayes Nash outcomes.
-- source:
--   Koessler, Laclau & Tomala, Interactive Information Design, SSRN working paper 3171992 (version of April 25, 2018), https://ssrn.com/abstract=3171992, p. 6, §2, paragraph beginning 'Let E_M(x)'

import Definitions.Def_InfoDesignGames_Existence_Model

namespace InfoDesignGames.Existence

theorem em_nonempty_convex (G : Game) (x : Profile G) :
    (EM G x).Nonempty ∧ Convex ℝ (EM G x) ∧
      EM G x = convexHull ℝ {y : Outcome G | ∃ σ, IsBNE G x σ ∧ y = outcomeOf G σ} := by sorry

end InfoDesignGames.Existence
