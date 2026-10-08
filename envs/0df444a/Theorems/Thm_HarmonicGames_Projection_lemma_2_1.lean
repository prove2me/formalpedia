-- Prove2me | Theorems.Thm_HarmonicGames_Projection_lemma_2_1
-- name    : HarmonicGames.Projection.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:14.105313+00:00
-- url     : https://prove2.me/theorems/10f5e0ad-d2ba-4a61-8128-65a1dcce44df
-- title:
--   Lemma 2.1 — utilities within $\epsilon_0$: $\epsilon_1$-equilibria transfer as $(2\epsilon_0+\epsilon_1)$-equilibria
-- statement:
--   Throughout, $\mathcal M$ is a finite set of players and each player $m$ has a nonempty finite strategy set $E^m$ with $h_m = |E^m|$ strategies; a game is given by utilities $u^m : E \to \mathbb R$ on the profiles $E = \prod_m E^m$.
--
--   **Lemma 2.1.** Let $G$ and $\hat G$ be two games with the same players and strategy sets and utilities $u^m$, $\hat u^m$. Suppose that, for some $\epsilon_0 \in \mathbb R$,
--   $$
--   |u^m(p) - \hat u^m(p)| \le \epsilon_0 \qquad \text{for every } m \in \mathcal M,\ p \in E .
--   $$
--   Then for every $\epsilon_1 \in \mathbb R$:
--   1. every $\epsilon_1$-equilibrium of $\hat G$ is a $(2\epsilon_0 + \epsilon_1)$-equilibrium of $G$;
--   2. every $\epsilon_1$-equilibrium of $G$ is a $(2\epsilon_0 + \epsilon_1)$-equilibrium of $\hat G$.
--
--   The lemma says that $\epsilon$-equilibria are stable under uniform perturbations of the utilities; Theorem 6.3 applies it with $\hat G$ the closest potential game.
--
--   **Formalization Note** The paper concludes "an $\epsilon$-equilibrium of $G$ for some $\epsilon \le 2\epsilon_0 + \epsilon_1$". Since the $\epsilon$-equilibrium condition (2) is monotone in $\epsilon$, this is equivalent to being a $(2\epsilon_0+\epsilon_1)$-equilibrium, which is how it is stated. Both directions ("and viceversa") are included.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 5, Lemma 2.1

import Mathlib
import Definitions.Def_HarmonicGames_Projection_EpsEquilibrium

namespace HarmonicGames.Projection

/-- **Lemma 2.1** (p. 5). Let `u` and `û` be the utilities of two games with the same players
and strategy sets, with `|u^m(p) - û^m(p)| ≤ ϵ₀` for every player `m` and profile `p`. Then every
`ϵ₁`-equilibrium of `û` is a `(2ϵ₀ + ϵ₁)`-equilibrium of `u`, and vice versa. -/
theorem lemma_2_1 {ι : Type} [Fintype ι] [DecidableEq ι] {E : ι → Type}
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u û : ι → (∀ m, E m) → ℝ) (ϵ₀ : ℝ) (h : ∀ m p, |u m p - û m p| ≤ ϵ₀) :
    (∀ (ϵ₁ : ℝ) (p : ∀ m, E m), IsEpsEquilibrium û ϵ₁ p →
        IsEpsEquilibrium u (2 * ϵ₀ + ϵ₁) p) ∧
      (∀ (ϵ₁ : ℝ) (p : ∀ m, E m), IsEpsEquilibrium u ϵ₁ p →
        IsEpsEquilibrium û (2 * ϵ₀ + ϵ₁) p) := by sorry

end HarmonicGames.Projection
