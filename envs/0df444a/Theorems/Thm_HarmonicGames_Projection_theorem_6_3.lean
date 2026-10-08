-- Prove2me | Theorems.Thm_HarmonicGames_Projection_theorem_6_3
-- name    : HarmonicGames.Projection.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:46:52.042977+00:00
-- url     : https://prove2.me/theorems/49077b89-8209-4798-af57-8152989dc071
-- title:
--   Theorem 6.3 — $\epsilon_1$-equilibria of the closest potential game are $(\max_m 2\alpha/\sqrt{h_m} + \epsilon_1)$-equilibria of the game, and conversely
-- statement:
--   Throughout, $\mathcal M$ is a finite set of players and each player $m$ has a nonempty finite strategy set $E^m$ with $h_m = |E^m|$ strategies; a game is given by utilities $u^m : E \to \mathbb R$ on the profiles $E = \prod_m E^m$. Let $\|\cdot\|_{M,E}$ be the weighted norm (56), $\|G\|_{M,E}^2 = \sum_m h_m \sum_{p \in E} u^m(p)^2$.
--
--   **Theorem 6.3.** Let $G$ be a game and $\hat G$ its closest potential game with respect to (56), and set $\alpha = \|G - \hat G\|_{M,E}$. Then for every $\epsilon_1 \in \mathbb R$:
--   1. every $\epsilon_1$-equilibrium of $\hat G$ is an $\epsilon$-equilibrium of $G$, and
--   2. every $\epsilon_1$-equilibrium of $G$ is an $\epsilon$-equilibrium of $\hat G$,
--
--   where
--   $$
--   \epsilon = \max_{m \in \mathcal M} \frac{2\alpha}{\sqrt{h_m}} + \epsilon_1 .
--   $$
--
--   The theorem links the approximate equilibria of an arbitrary game to the equilibria of its closest potential game, whose equilibrium and dynamical properties are well understood; the distance $\alpha$ to the set of potential games measures how far the conclusion degrades.
--
--   **Formalization Note** The paper says "an $\epsilon$-equilibrium of $G$ for some $\epsilon \le \max_m 2\alpha/\sqrt{h_m} + \epsilon_1$"; since condition (2) is monotone in $\epsilon$, this is equivalent to the statement with equality, which is how it is formalized. The maximum is over players, so a nonempty set of players is assumed (with no players every profile is an equilibrium of every game). Strategy sets are nonempty, so $h_m \ge 1$. The hypothesis is that $\hat G$ is a closest potential game in the sense of the Section 6 definitions, not merely some potential game; such a $\hat G$ exists by Theorem 6.2.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 36, Theorem 6.3

import Mathlib
import Definitions.Def_HarmonicGames_Projection_EpsEquilibrium
import Definitions.Def_HarmonicGames_Projection_Closest

namespace HarmonicGames.Projection

/-- **Theorem 6.3** (p. 36). Let `û` be the closest potential game to the game `u` with respect
to the norm (56), let `h_m = |E^m|`, and let `α = ‖u - û‖_{M,E}`. Then every `ϵ₁`-equilibrium of
`û` is a `(max_m 2α/√h_m + ϵ₁)`-equilibrium of `u`, and vice versa. -/
theorem theorem_6_3 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u û : ι → (∀ m, E m) → ℝ) (hû : IsClosestPotential E u û) :
    (∀ (ϵ₁ : ℝ) (p : ∀ m, E m), IsEpsEquilibrium û ϵ₁ p →
        IsEpsEquilibrium u
          (Finset.univ.sup' Finset.univ_nonempty
            (fun m => 2 * normME E (u - û) / Real.sqrt (Fintype.card (E m))) + ϵ₁) p) ∧
      (∀ (ϵ₁ : ℝ) (p : ∀ m, E m), IsEpsEquilibrium u ϵ₁ p →
        IsEpsEquilibrium û
          (Finset.univ.sup' Finset.univ_nonempty
            (fun m => 2 * normME E (u - û) / Real.sqrt (Fintype.card (E m))) + ϵ₁) p) := by sorry

end HarmonicGames.Projection
