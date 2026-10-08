-- Prove2me | Theorems.Thm_HarmonicGames_GenericPure_proposition_5_1
-- name    : HarmonicGames.GenericPure.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:37.055631+00:00
-- url     : https://prove2.me/theorems/74955fb9-18a5-4881-9860-935647d3e8f5
-- title:
--   Proposition 5.1 — harmonic games generically do not have pure Nash equilibria
-- statement:
--   Consider finite games with player set $\mathcal M$ and nonempty finite strategy sets $E^m$, in which at least two distinct players have at least two strategies each. A game is **harmonic** if its utilities lie in $\mathcal H \oplus \mathcal N$, a finite-dimensional real vector space. Let $\mu$ be any additive Haar measure on $\mathcal H \oplus \mathcal N$ (for instance Lebesgue measure in a linear coordinate system). Then
--
--   $$
--   \mu\big(\{\, u \in \mathcal H \oplus \mathcal N \;:\; u \text{ has a pure Nash equilibrium} \,\}\big) = 0 .
--   $$
--
--   That is, harmonic games generically do not have pure Nash equilibria: in the paper's words, the statement is "true for almost all harmonic games, except possibly for a set of measure zero". The exceptional set is not empty: the zero game is harmonic and every profile is a pure Nash equilibrium of it.
--
--   The paper leaves implicit that at least two players have at least two strategies; its proof uses this through $\dim \mathcal H > 0$ ("We reach a contradiction since dimension of $\mathcal H$ is larger than zero"). The hypothesis is necessary: if at most one player has more than one strategy, then $\mathcal H = 0$, every harmonic game is nonstrategic, and every strategy profile is a pure Nash equilibrium of every harmonic game.
--
--   **Formalization Note** The measure lives on the subspace $\mathcal H \oplus \mathcal N$ (the subtype `↥(H ⊔ N)` with the Borel σ-algebra of its subspace topology), not on all of $C_0^M$: a proper subspace of $C_0^M$ is itself Lebesgue-null there, which would make the statement empty. All additive Haar measures on a finite-dimensional space have the same null sets, so the statement does not depend on the choice of $\mu$. Pure Nash equilibrium is `AGT.IsPureNash` from `agt_games`, condition (1) of the paper.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 23, Section 5.2.1, Proposition 5.1 (with the definition of "generically" on the same page)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_GenericPure_Games

namespace HarmonicGames.GenericPure

open MeasureTheory

/-- **Proposition 5.1** (p. 23). Harmonic games generically do not have pure Nash equilibria:
for every additive Haar measure `μ` on the finite-dimensional space `H ⊕ N` of harmonic games,
the set of harmonic games that have a pure Nash equilibrium is `μ`-null.

The hypothesis `h2` (at least two distinct players have at least two strategies each) is left
implicit in the paper; its proof uses it through `dim H > 0`. -/
theorem proposition_5_1 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (h2 : ∃ m₁ m₂ : ι, m₁ ≠ m₂ ∧ 2 ≤ Fintype.card (E m₁) ∧ 2 ≤ Fintype.card (E m₂))
    (μ : Measure (harmonicGames E)) [μ.IsAddHaarMeasure] :
    μ {v : harmonicGames E | ∃ p : ∀ m, E m, AGT.IsPureNash (payoff E (v : HarmonicGames.Decomposition.Games E)) p} = 0 := by sorry

end HarmonicGames.GenericPure
