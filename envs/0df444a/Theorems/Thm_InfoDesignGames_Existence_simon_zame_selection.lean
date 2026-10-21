-- Prove2me | Theorems.Thm_InfoDesignGames_Existence_simon_zame_selection
-- name    : InfoDesignGames.Existence.simon_zame_selection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:36.310877+00:00
-- url     : https://prove2.me/theorems/bdf2d34e-d1c4-4469-9d13-4db328f75445
-- title:
--   Proof of Theorem 1, p. 7 — Simon–Zame measurable payoff selection with mixed equilibrium
-- statement:
--   Let $\mathcal U(x)$ be the designer payoff correspondence of a finite information design game. There is a Borel measurable payoff selection $U^*$ that belongs to $\mathcal U(x)$ at every experiment profile $x$, and its induced normal-form game admits an independent mixed Nash equilibrium $\zeta$:
--
--   $$\exists U^*,\zeta,\quad U^*(x)\in\mathcal U(x)\ \forall x,\quad U^*\text{ is Borel measurable},\quad \zeta\text{ is a mixed Nash equilibrium for }U^*.$$
--
--   This is the specific application of Simon and Zame's theorem used in the proof of Theorem 1.
--
--   **Formalization Note** Each $\zeta_i$ is a Borel probability measure on the full experiment space $X_i$, with deviations to every other probability measure. Payoff integrability is part of the mixed-equilibrium predicate.
-- source:
--   Koessler, Laclau & Tomala, Interactive Information Design, SSRN working paper 3171992 (version of April 25, 2018), https://ssrn.com/abstract=3171992, p. 7, proof of Theorem 1, Simon–Zame sentence

import Definitions.Def_InfoDesignGames_Existence_Model

namespace InfoDesignGames.Existence

theorem simon_zame_selection (G : Game) :
    ∃ Ustar : Profile G → G.ι → ℝ,
      Measurable Ustar ∧ (∀ x, Ustar x ∈ payoffSet G x) ∧
        ∃ ζ : MixedProfile G, IsMixedNashDesigners G Ustar ζ := by sorry

end InfoDesignGames.Existence
