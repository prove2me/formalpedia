-- Prove2me | Theorems.Thm_HarmonicGames_Pareto_lemma_5_4
-- name    : HarmonicGames.Pareto.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:30.249042+00:00
-- url     : https://prove2.me/theorems/c07debec-20a4-4ca3-b4ab-084af5bb1aeb
-- title:
--   Lemma 5.4 — changing only the nonstrategic component can make every payoff zero at every pure Nash equilibrium
-- statement:
--   Let $G$ be a finite game with players $\mathcal M$, nonempty finite strategy sets $E^m$ and utilities $u = (u^m)_m$. Then there exists a game $\hat G$ with utilities $\hat u = (\hat u^m)_m$ such that
--
--   1. the potential and harmonic components of $\hat G$ are identical to those of $G$:
--
--   $$
--   D^\dagger \delta_0 \delta_0^\dagger D \hat u = D^\dagger \delta_0 \delta_0^\dagger D u, \qquad D^\dagger (I - \delta_0 \delta_0^\dagger) D \hat u = D^\dagger (I - \delta_0 \delta_0^\dagger) D u ;
--   $$
--
--   2. in $\hat G$ all players get zero payoff at all strategy profiles that are pure Nash equilibria of $G$: $\hat u^m(p) = 0$ for every $m \in \mathcal M$ and every pure Nash equilibrium $p$ of $G$.
--
--   The lemma is the normalisation step of Section 5.3: it shows that the payoff levels at equilibria are fixed by the nonstrategic component alone, which Theorem 5.9 then exploits.
--
--   **Formalization Note** Pure Nash equilibrium of $G$ is `AGT.IsPureNash (payoff E u)`, condition (1) of the paper. The components are the maps of Theorem 4.1, with pseudoinverses taken for the unweighted inner product on games. If $G$ has no pure Nash equilibrium, condition 2 is vacuous and $\hat u = u$ works; this agrees with the paper.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 31, Lemma 5.4

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_Pareto_Games

namespace HarmonicGames.Pareto

/-- **Lemma 5.4** (p. 31). For every game `u` there is a game `û` with (i) the same potential
and harmonic components as `u` and (ii) `û^m(p) = 0` for every player `m` at every strategy
profile `p` that is a pure Nash equilibrium of `u`. -/
theorem lemma_5_4 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) :
    ∃ û : HarmonicGames.Decomposition.Games E, HarmonicGames.Decomposition.potentialComponent E û = HarmonicGames.Decomposition.potentialComponent E u ∧
      HarmonicGames.Decomposition.harmonicComponent E û = HarmonicGames.Decomposition.harmonicComponent E u ∧
      ∀ p : ∀ m, E m, AGT.IsPureNash (HarmonicGames.GenericPure.payoff E u) p → ∀ m, HarmonicGames.GenericPure.payoff E û m p = 0 := by sorry

end HarmonicGames.Pareto
