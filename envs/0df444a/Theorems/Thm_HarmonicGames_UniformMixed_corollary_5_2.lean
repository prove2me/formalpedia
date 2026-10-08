-- Prove2me | Theorems.Thm_HarmonicGames_UniformMixed_corollary_5_2
-- name    : HarmonicGames.UniformMixed.corollary_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:39.326983+00:00
-- url     : https://prove2.me/theorems/ffe1cc7c-45ff-4df7-bbd0-665609bbe9c4
-- title:
--   Corollary 5.2 — at a mixed Nash equilibrium of a harmonic game every player is indifferent among all pure strategies
-- statement:
--   Let $G$ be a finite game with players $\mathcal M$, nonempty finite strategy sets $E^m$ and utilities $u = (u^m)_m$, and suppose $G$ is a **harmonic game**, $u \in \mathcal H \oplus \mathcal N$. Let $x = \{x^m\}_m \in \prod_m \Delta E^m$ be a mixed strategy profile. Then $x$ is a mixed Nash equilibrium (Definition 5.1.1) if and only if
--
--   $$
--   u^m(x^m, x^{-m}) = u^m(p^m, x^{-m}) \qquad \text{for all } p^m \in E^m \text{ and } m \in \mathcal M \qquad (42),
--   $$
--
--   where $u^m(x^m,x^{-m}) = \sum_{p} u^m(p)\prod_k x^k(p^k)$ is the mixed extension (34) and $u^m(p^m, x^{-m})$ the payoff (35) of the pure strategy $p^m$ against $x^{-m}$.
--
--   Unlike general games, where equilibrium indifference holds only on the support of each mixed strategy, in a harmonic game each player is indifferent among all of its pure strategies at any mixed equilibrium.
--
--   **Formalization Note** The mixed extension is `AGT.expectedPayoff`; the payoff (35) and Definition 5.1.1 (with pure deviations) are from the mission's definition file.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 26, Corollary 5.2, (42)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games
import Definitions.Def_HarmonicGames_UniformMixed_Mixed

namespace HarmonicGames.UniformMixed

/-- **Corollary 5.2** (p. 26): in a harmonic game `u ∈ H ⊕ N`, a mixed strategy profile
`x ∈ ∏_m ΔE^m` is a mixed Nash equilibrium (Definition 5.1.1) if and only if
`u^m(x^m, x^{-m}) = u^m(p^m, x^{-m})` for all `p^m ∈ E^m` and all `m` (42), with `u^m(x)`
the mixed extension (34) and `u^m(p^m, x^{-m})` the payoff (35). -/
theorem corollary_5_2 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hu : u ∈ HarmonicGames.GenericPure.harmonicGames E) (x : ∀ m, E m → ℝ) (hx : AGT.IsMixedProfile x) :
    IsMixedNashEquilibrium (HarmonicGames.GenericPure.payoff E u) x ↔
      ∀ (m : ι) (a : E m), AGT.expectedPayoff (HarmonicGames.GenericPure.payoff E u) x m = mixedVsPure (HarmonicGames.GenericPure.payoff E u) x m a := by sorry

end HarmonicGames.UniformMixed
