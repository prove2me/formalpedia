-- Prove2me | Theorems.Thm_HarmonicGames_UniformMixed_remark_5_2_all_harmonic
-- name    : HarmonicGames.UniformMixed.remark_5_2_all_harmonic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:08.990745+00:00
-- url     : https://prove2.me/theorems/152104c5-eadb-42b1-93bc-2a4969e14afa
-- title:
--   Remark after Proposition 5.2 — (i) ⇔ (ii) holds for all harmonic games
-- statement:
--   Let $G$ be a finite game with players $\mathcal M$, nonempty finite strategy sets $E^m$ and utilities $u = (u^m)_m$, and suppose $G$ is a **harmonic game**, $u \in \mathcal H \oplus \mathcal N$ (not necessarily normalized). Let $x \in \Delta E$ be a probability distribution on strategy profiles. Then $x$ is a correlated equilibrium (Definition 5.1.2) if and only if, for all $m \in \mathcal M$ and $p^m, q^m \in E^m$,
--
--   $$
--   \sum_{p^{-m}} \big(u^m(p^m,p^{-m}) - u^m(q^m,p^{-m})\big)\, x(p^m,p^{-m}) = 0 \qquad (36).
--   $$
--
--   The paper observes this after the proof of Proposition 5.2, whose normalization hypothesis is used only for the equivalence with (37). It is the form used in Corollary 5.2.
--
--   **Formalization Note** Correlated equilibrium is the referenced `HartSchmeidler.Finite.IsCorrelatedEq`; sums over $p^{-m}$ are sums over the profiles with $p^m$ fixed.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 26, Section 5.2.2, remark following the proof of Proposition 5.2 (unnumbered)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HartSchmeidler_Finite_Game
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games

namespace HarmonicGames.UniformMixed

/-- **Remark after Proposition 5.2** (§5.2.2, p. 26): for every harmonic game `u ∈ H ⊕ N`
(not necessarily normalized) and every probability distribution `x ∈ ΔE`, `x` is a
correlated equilibrium if and only if, for all `m` and `p^m, q^m ∈ E^m`,
`∑_{p^{-m}} (u^m(p^m, p^{-m}) - u^m(q^m, p^{-m})) x(p^m, p^{-m}) = 0` (36). -/
theorem remark_5_2_all_harmonic {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hu : u ∈ HarmonicGames.GenericPure.harmonicGames E) (x : (∀ k, E k) → ℝ) (hx : AGT.IsLottery x) :
    HartSchmeidler.Finite.IsCorrelatedEq (HarmonicGames.GenericPure.payoff E u) x ↔
      ∀ (m : ι) (a b : E m),
        ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
          (HarmonicGames.GenericPure.payoff E u m p - HarmonicGames.GenericPure.payoff E u m (Function.update p m b)) * x p = 0 := by sorry

end HarmonicGames.UniformMixed
