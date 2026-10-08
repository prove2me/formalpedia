-- Prove2me | Theorems.Thm_HarmonicGames_Decomposition_lemma_4_1
-- name    : HarmonicGames.Decomposition.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:53:44.659766+00:00
-- url     : https://prove2.me/theorems/e0635950-460b-48d9-9c6a-1f8f4872eeca
-- title:
--   Lemma 4.1 — $\Delta_{0,m} = h_m\Pi_m$
-- statement:
--   For a finite game with players $\mathcal M$ and nonempty finite strategy sets $E^m$, let $D_m : C_0 \to C_1$ be the gradient along $m$-comparable pairs of profiles, $\Delta_{0,m} = D_m^* D_m$ the Laplacian of the graph of $m$-comparable profiles, and $\Pi_m = D_m^\dagger D_m$ (adjoint and Moore–Penrose pseudoinverse for the inner products (7)).
--
--   **Lemma 4.1.** With $h_m = |E^m|$ the number of strategies of player $m$,
--
--   $$
--   \Delta_{0,m} = h_m\,\Pi_m .
--   $$
--
--   The Laplacian of each player's comparison graph is thus a multiple of the orthogonal projection onto $(\ker D_m)^\perp$; this is what makes the pseudoinverses in the decomposition explicit.
--
--   **Formalization Note** $h_m$ is `Fintype.card (E m)`; adjoints and pseudoinverses are for the $\tfrac12$-weighted inner product on edge flows and the standard one on $C_0$.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 15, Lemma 4.1

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_HarmonicGames_Decomposition_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games

namespace HarmonicGames.Decomposition

theorem lemma_4_1 (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (m : ι) :
    Delta0m E m = (Fintype.card (E m) : ℝ) • Pim E m := by sorry

end HarmonicGames.Decomposition
