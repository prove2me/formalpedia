-- Prove2me | Theorems.Thm_HarmonicGames_Pareto_theorem_5_9
-- name    : HarmonicGames.Pareto.theorem_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:15.201007+00:00
-- url     : https://prove2.me/theorems/1c122f98-5637-41c9-8fec-6c100c842502
-- title:
--   Theorem 5.9 — changing only the nonstrategic component makes the pure Nash equilibria coincide with the Pareto optimal profiles
-- statement:
--   Let $G$ be a finite game with players $\mathcal M$, nonempty finite strategy sets $E^m$ and utilities $u = (u^m)_m$, and assume that $G$ has at least one pure Nash equilibrium. Then there exists a game $\bar G$ with utilities $\bar u = (\bar u^m)_m$ such that
--
--   1. the potential and harmonic components of $\bar G$ are identical to those of $G$:
--
--   $$
--   D^\dagger \delta_0 \delta_0^\dagger D \bar u = D^\dagger \delta_0 \delta_0^\dagger D u, \qquad D^\dagger (I - \delta_0 \delta_0^\dagger) D \bar u = D^\dagger (I - \delta_0 \delta_0^\dagger) D u ;
--   $$
--
--   2. in $\bar G$ the set of pure Nash equilibria coincides with the set of Pareto optimal strategy profiles: for every profile $p$,
--
--   $$
--   p \text{ is a pure Nash equilibrium of } \bar G \iff p \text{ is Pareto optimal in } \bar G .
--   $$
--
--   **The paper leaves implicit that $G$ has a pure Nash equilibrium.** The hypothesis is necessary: a finite game always has a Pareto optimal profile (a maximiser of $\sum_m u^m$), while a game with no pure Nash equilibrium (matching pennies) has none in any game with the same potential and harmonic components, since those components determine the pairwise comparisons; so condition 2 cannot hold. The paper's proof uses an equilibrium when it argues that "deviation to a NE increases the payoff of at least one player".
--
--   The theorem shows that the nonstrategic component, which has no effect on equilibria, fully controls their efficiency: it can always be chosen so that the equilibria are exactly the Pareto optimal profiles.
--
--   **Formalization Note** Pure Nash equilibrium is `AGT.IsPureNash` (condition (1)), Pareto optimality is Definition 5.3, both applied to `payoff E ū`. The components are the maps of Theorem 4.1 with pseudoinverses for the unweighted inner product on games. Condition 2 is an equivalence, not one inclusion.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 32, Theorem 5.9

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_Pareto_Games
import Definitions.Def_HarmonicGames_Pareto_IsParetoOptimal

namespace HarmonicGames.Pareto

/-- **Theorem 5.9** (p. 32). Let `u` be a game that has a pure Nash equilibrium (the paper
leaves this hypothesis implicit; without it the statement fails, e.g. for matching pennies).
Then there is a game `ū` with (i) the same potential and harmonic components as `u` and (ii) in
`ū` a strategy profile is a pure Nash equilibrium iff it is Pareto optimal. -/
theorem theorem_5_9 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hNE : ∃ p : ∀ m, E m, AGT.IsPureNash (HarmonicGames.GenericPure.payoff E u) p) :
    ∃ ū : HarmonicGames.Decomposition.Games E, HarmonicGames.Decomposition.potentialComponent E ū = HarmonicGames.Decomposition.potentialComponent E u ∧
      HarmonicGames.Decomposition.harmonicComponent E ū = HarmonicGames.Decomposition.harmonicComponent E u ∧
      ∀ p : ∀ m, E m, AGT.IsPureNash (HarmonicGames.GenericPure.payoff E ū) p ↔ IsParetoOptimal (HarmonicGames.GenericPure.payoff E ū) p := by sorry

end HarmonicGames.Pareto
