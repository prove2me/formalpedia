-- Prove2me | Theorems.Thm_HarmonicGames_Projection_theorem_6_1
-- name    : HarmonicGames.Projection.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:46:49.453001+00:00
-- url     : https://prove2.me/theorems/7476ab64-00b5-4018-a70b-f859048e87e6
-- title:
--   Theorem 6.1 — $\mathcal P \perp \mathcal H \perp \mathcal N$ under the weighted inner product (55)
-- statement:
--   Throughout, $\mathcal M$ is a finite set of players and each player $m$ has a nonempty finite strategy set $E^m$ with $h_m = |E^m|$ strategies; a game is given by utilities $u^m : E \to \mathbb R$ on the profiles $E = \prod_m E^m$. Let $\mathcal P$, $\mathcal H$, $\mathcal N$ be the potential, harmonic and nonstrategic subspaces of Definition 4.2, (28), and $\langle \cdot, \cdot \rangle_{M,E}$ the weighted inner product (55), $\langle G, \hat G\rangle_{M,E} = \sum_m h_m \sum_{p \in E} u^m(p) \hat u^m(p)$.
--
--   **Theorem 6.1.** Under the inner product (55), the three subspaces are pairwise orthogonal:
--   $$
--   \langle G_{\mathcal P}, G_{\mathcal H} \rangle_{M,E} = \langle G_{\mathcal P}, G_{\mathcal N} \rangle_{M,E} = \langle G_{\mathcal H}, G_{\mathcal N} \rangle_{M,E} = 0
--   $$
--   for all $G_{\mathcal P} \in \mathcal P$, $G_{\mathcal H} \in \mathcal H$, $G_{\mathcal N} \in \mathcal N$.
--
--   The weights $h_m$ matter: the subspaces are defined through operators that use the unweighted inner product, and $\mathcal P \perp \mathcal H$ can fail for the unweighted inner product when the $h_m$ differ. The orthogonality makes the decomposition $\mathcal P \oplus \mathcal H \oplus \mathcal N$ orthogonal, so that the closest potential and harmonic games of Theorem 6.2 are orthogonal projections.
--
--   **Formalization Note** Membership in the subspaces is for the game viewed in $C_0^M$ (`toGames E`); the inner product is the plain function `innerME`.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 35, Theorem 6.1

import Mathlib
import Definitions.Def_HarmonicGames_Projection_Closest

namespace HarmonicGames.Projection

/-- **Theorem 6.1** (p. 35). Under the weighted inner product (55),
`⟨G, Ĝ⟩_{M,E} = ∑_m h_m ⟨u^m, û^m⟩`, the potential, harmonic and nonstrategic subspaces
`P`, `H`, `N` of (28) are pairwise orthogonal. -/
theorem theorem_6_1 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] :
    (∀ a b : ι → (∀ m, E m) → ℝ, toGames E a ∈ HarmonicGames.Decomposition.potentialSubspace E →
        toGames E b ∈ HarmonicGames.Decomposition.harmonicSubspace E → innerME E a b = 0) ∧
      (∀ a b : ι → (∀ m, E m) → ℝ, toGames E a ∈ HarmonicGames.Decomposition.potentialSubspace E →
        toGames E b ∈ HarmonicGames.Decomposition.nonstrategicSubspace E → innerME E a b = 0) ∧
      (∀ a b : ι → (∀ m, E m) → ℝ, toGames E a ∈ HarmonicGames.Decomposition.harmonicSubspace E →
        toGames E b ∈ HarmonicGames.Decomposition.nonstrategicSubspace E → innerME E a b = 0) := by sorry

end HarmonicGames.Projection
