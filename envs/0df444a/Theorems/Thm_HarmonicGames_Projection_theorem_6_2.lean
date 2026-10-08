-- Prove2me | Theorems.Thm_HarmonicGames_Projection_theorem_6_2
-- name    : HarmonicGames.Projection.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:46:56.465877+00:00
-- url     : https://prove2.me/theorems/f7c8ff04-0025-438b-b4b0-dfd0625ae39d
-- title:
--   Theorem 6.2 — closest potential game $\Pi_m\varphi + (I-\Pi_m)u^m$ and closest harmonic game $u^m - \Pi_m\varphi$
-- statement:
--   Throughout, $\mathcal M$ is a finite set of players and each player $m$ has a nonempty finite strategy set $E^m$ with $h_m = |E^m|$ strategies; a game is given by utilities $u^m : E \to \mathbb R$ on the profiles $E = \prod_m E^m$. Let $D$ be the operator (21), $\delta_0$ the combinatorial gradient of the game graph, $\Pi_m = D_m^\dagger D_m$, and $\|\cdot\|_{M,E}$ the norm (56). For a game $G$ with utilities $\{u^m\}_m$ put
--   $$
--   \varphi = \delta_0^\dagger D u \in C_0 .
--   $$
--
--   **Theorem 6.2.** With respect to the norm (56):
--   1. the closest potential game to $G$ has utilities $\Pi_m \varphi + (I - \Pi_m) u^m$ for all $m \in \mathcal M$;
--   2. the closest harmonic game to $G$ has utilities $u^m - \Pi_m \varphi$ for all $m \in \mathcal M$.
--
--   Each item is stated as a characterization: a game $\hat G$ is a closest potential game to $G$ (a potential game minimizing $\|G - \hat G\|_{M,E}$ over all potential games) if and only if $\hat u^m = \Pi_m \varphi + (I - \Pi_m) u^m$ for every $m$; likewise for harmonic games (games in $\mathcal H \oplus \mathcal N$). This gives at once that the closest game exists, is unique, and is given by the formula. Note that $\Pi_m$ is applied to the same function $\varphi$ for every player.
--
--   The closed forms show that the closest potential game keeps the nonstrategic part $(I - \Pi_m) u^m$ of the game and replaces its strategic part by the preferences induced by the potential $\varphi$.
--
--   **Formalization Note** $\delta_0^\dagger$ and $D_m^\dagger$ are Moore–Penrose pseudoinverses for the unweighted inner products of Sections 3–4; "closest" refers to the weighted norm (56). The definite article in "the closest potential game" is rendered by the "if and only if".
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 36, Theorem 6.2

import Mathlib
import Definitions.Def_HarmonicGames_Projection_Closest

namespace HarmonicGames.Projection

/-- **Theorem 6.2** (p. 36). Let `u` be a game and `φ = δ0† D u`. With respect to the norm (56):
1. the closest potential game to `u` is unique and has utilities `Π_m φ + (I - Π_m) u^m`;
2. the closest harmonic game to `u` is unique and has utilities `u^m - Π_m φ`. -/
theorem theorem_6_2 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : ι → (∀ m, E m) → ℝ) (φ : HarmonicGames.Decomposition.Util E) (hφ : φ = HarmonicGames.Decomposition.potentialFunction E (toGames E u)) :
    (∀ û : ι → (∀ m, E m) → ℝ, IsClosestPotential E u û ↔
        û = fun m p => HarmonicGames.Decomposition.Pim E m φ p + (u m p - HarmonicGames.Decomposition.Pim E m (WithLp.toLp 2 (u m)) p)) ∧
      (∀ û : ι → (∀ m, E m) → ℝ, IsClosestHarmonic E u û ↔
        û = fun m p => u m p - HarmonicGames.Decomposition.Pim E m φ p) := by sorry

end HarmonicGames.Projection
