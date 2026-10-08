-- Prove2me | Theorems.Thm_HarmonicGames_UniformMixed_theorem_5_4
-- name    : HarmonicGames.UniformMixed.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:15.378988+00:00
-- url     : https://prove2.me/theorems/9ed4e719-a1d6-42bf-b5ec-cc096d1be86d
-- title:
--   Theorem 5.4 — in every harmonic game the uniformly mixed strategy profile is a mixed Nash equilibrium
-- statement:
--   Let $G$ be a finite game with a finite set of players $\mathcal M$, for each player $m$ a nonempty finite strategy set $E^m$ with $h_m = |E^m|$ elements, and utilities $u = (u^m)_m$, and suppose $G$ is a **harmonic game**: $u \in \mathcal H \oplus \mathcal N$, the sum of the harmonic and nonstrategic subspaces of Definition 4.2. Let $x$ be the **uniformly mixed strategy profile**, $x^m(q^m) = 1/h_m$ for every player $m$ and every $q^m \in E^m$ (Definition 5.2). Then $x$ is a mixed Nash equilibrium of $G$ (Definition 5.1.1):
--
--   $$
--   u^m(x^m, x^{-m}) \;\ge\; u^m(p^m, x^{-m}) \qquad \text{for all } m \in \mathcal M,\ p^m \in E^m .
--   $$
--
--   Rock–paper–scissors and matching pennies are instances; the theorem says the uniform profile is an equilibrium of every harmonic game, whatever the number of players and strategies.
--
--   **Formalization Note** Harmonic game means membership in the submodule sum $\mathcal H \sqcup \mathcal N$ of the game space $C_0^M$, with $\mathcal H$, $\mathcal N$ defined by (28). The mixed extension is `AGT.expectedPayoff`; the pure-deviation payoff (35) and the equilibrium notion are from the mission's definition file. The paper takes $E^m = \{1,\dots,h_m\}$, so every strategy set is nonempty; the hypothesis `[∀ m, Nonempty (E m)]` makes this explicit (otherwise $1/h_m = 1/0 = 0$ would not be a probability).
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 27, Theorem 5.4

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games
import Definitions.Def_HarmonicGames_UniformMixed_Mixed

namespace HarmonicGames.UniformMixed

/-- **Theorem 5.4** (p. 27): in every harmonic game `u ∈ H ⊕ N`, the uniformly mixed strategy
profile (Definition 5.2), in which each player `m` plays each of its `h_m` strategies with
probability `1/h_m`, is a mixed Nash equilibrium (Definition 5.1.1). -/
theorem theorem_5_4 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hu : u ∈ HarmonicGames.GenericPure.harmonicGames E) :
    IsMixedNashEquilibrium (HarmonicGames.GenericPure.payoff E u) (uniformProfile E) := by sorry

end HarmonicGames.UniformMixed
