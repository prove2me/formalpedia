-- Prove2me | Theorems.Thm_HarmonicGames_Projection_theorem_5_1
-- name    : HarmonicGames.Projection.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:46:50.605926+00:00
-- url     : https://prove2.me/theorems/036c3d9f-b554-4f66-bd47-1ba451a9a34f
-- title:
--   Theorem 5.1 — the set of potential games equals $\mathcal P \oplus \mathcal N$
-- statement:
--   Throughout, $\mathcal M$ is a finite set of players and each player $m$ has a nonempty finite strategy set $E^m$ with $h_m = |E^m|$ strategies; a game is given by utilities $u^m : E \to \mathbb R$ on the profiles $E = \prod_m E^m$. Write $C_0^M$ for the space of games, and $\mathcal P$, $\mathcal N$ for the potential and nonstrategic subspaces of Definition 4.2, (28).
--
--   **Theorem 5.1.** The set of potential games is equal to the subspace $\mathcal P \oplus \mathcal N$: for every game $u$,
--   $$
--   u \text{ is a potential game (Definition 2.1)} \iff u \in \mathcal P \oplus \mathcal N .
--   $$
--
--   Here a potential game is one admitting $\varphi : E \to \mathbb R$ with $\varphi(p^m, p^{-m}) - \varphi(q^m, p^{-m}) = u^m(p^m, p^{-m}) - u^m(q^m, p^{-m})$ for all $m$, $p^m, q^m \in E^m$, $p^{-m}$. The theorem identifies the set over which the closest potential game of Section 6 is taken as a linear subspace, which is what makes the projection well defined.
--
--   **Formalization Note** Potential games are the published `MondererShapley.ClosedPath.IsPotentialGame`. The sum $\mathcal P \oplus \mathcal N$ is the submodule sup `potentialSubspace E ⊔ nonstrategicSubspace E` (that the sum is direct is part of Theorem 4.1, not of this statement). Strategy sets are assumed nonempty, as the paper's $E^m = \{1, \dots, h_m\}$ are.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 22, Theorem 5.1

import Mathlib
import Definitions.Def_HarmonicGames_Projection_Closest

namespace HarmonicGames.Projection

/-- **Theorem 5.1** (p. 22). The set of potential games (Definition 2.1) is equal to the
subspace `P ⊕ N`: a game `u` is a potential game if and only if, as an element of `C0^M`, it lies
in the sum of the potential subspace `P` and the nonstrategic subspace `N` of (28). -/
theorem theorem_5_1 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : ι → (∀ m, E m) → ℝ) :
    MondererShapley.ClosedPath.IsPotentialGame u ↔
      toGames E u ∈ HarmonicGames.Decomposition.potentialSubspace E ⊔ HarmonicGames.Decomposition.nonstrategicSubspace E := by sorry

end HarmonicGames.Projection
