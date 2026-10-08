-- Prove2me | Theorems.Thm_HarmonicGames_Pareto_same_components_same_pure_nash
-- name    : HarmonicGames.Pareto.same_components_same_pure_nash
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:17.305303+00:00
-- url     : https://prove2.me/theorems/613db658-a2a1-4402-870e-bdf7015b295e
-- title:
--   §5.3, p. 32 — games differing only in their nonstrategic components have the same pure Nash equilibria
-- statement:
--   Let $\mathcal M$ be a finite set of players with nonempty finite strategy sets $E^m$, and let $u = (u^m)_m$ and $v = (v^m)_m$ be two games on them. Suppose $u$ and $v$ have the same potential component and the same harmonic component (Theorem 4.1):
--
--   $$
--   D^\dagger \delta_0 \delta_0^\dagger D u = D^\dagger \delta_0 \delta_0^\dagger D v, \qquad D^\dagger (I - \delta_0 \delta_0^\dagger) D u = D^\dagger (I - \delta_0 \delta_0^\dagger) D v .
--   $$
--
--   Then a strategy profile $p$ is a pure Nash equilibrium of $u$ if and only if it is a pure Nash equilibrium of $v$, where $p$ is a pure Nash equilibrium of $u$ when $u^m(q^m, p^{-m}) \le u^m(p)$ for every player $m$ and every $q^m \in E^m$.
--
--   The paper states this in Section 5.3: games that differ only in their nonstrategic components have identical pairwise comparisons, hence the same Nash equilibria. It is the bridge between the language of components, in which Lemma 5.4 and Theorem 5.9 are stated, and the equilibrium sets they speak about.
--
--   **Formalization Note** Pure Nash equilibrium is `AGT.IsPureNash` of the published `agt_games` bundle, applied to `payoff E u`; it is condition (1) of the paper. "Differ only in their nonstrategic components" is rendered as equality of the two component maps, exactly as in Lemma 5.4 and Theorem 5.9.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 32, Section 5.3 (proof of Theorem 5.9: "Games that differ only in nonstrategic components have identical pairwise comparisons, hence the set of Nash equilibria (NE) is the same for such games"); also p. 32, paragraph after Lemma 5.4

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_Pareto_Games

namespace HarmonicGames.Pareto

/-- **§5.3, p. 32** (proof of Theorem 5.9). Games that differ only in their nonstrategic
components have the same pure Nash equilibria: if `u` and `v` have the same potential component
and the same harmonic component (Theorem 4.1), then a strategy profile is a pure Nash equilibrium
of `u` iff it is one of `v`. -/
theorem same_components_same_pure_nash {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u v : HarmonicGames.Decomposition.Games E) (hP : HarmonicGames.Decomposition.potentialComponent E u = HarmonicGames.Decomposition.potentialComponent E v)
    (hH : HarmonicGames.Decomposition.harmonicComponent E u = HarmonicGames.Decomposition.harmonicComponent E v) (p : ∀ m, E m) :
    AGT.IsPureNash (HarmonicGames.GenericPure.payoff E u) p ↔ AGT.IsPureNash (HarmonicGames.GenericPure.payoff E v) p := by sorry

end HarmonicGames.Pareto
