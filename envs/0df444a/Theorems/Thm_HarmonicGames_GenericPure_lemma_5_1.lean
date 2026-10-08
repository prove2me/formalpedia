-- Prove2me | Theorems.Thm_HarmonicGames_GenericPure_lemma_5_1
-- name    : HarmonicGames.GenericPure.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:53.049243+00:00
-- url     : https://prove2.me/theorems/cbce9b27-4386-46a4-9e93-3bf19ea7713e
-- title:
--   Lemma 5.1 — at a pure Nash equilibrium of a harmonic game every player is indifferent among all strategies
-- statement:
--   Let $G = \langle \mathcal M, \{E^m\}, \{u^m\}\rangle$ be a finite game with nonempty strategy sets, and suppose $G$ is a **harmonic game**, i.e. its utility collection $u = (u^m)_m$ lies in $\mathcal H \oplus \mathcal N$. Let $p$ be a pure Nash equilibrium of $G$: $u^m(p^m, p^{-m}) \ge u^m(q^m, p^{-m})$ for every player $m$ and every $q^m \in E^m$. Then
--
--   $$
--   u^m(p^m, p^{-m}) = u^m(q^m, p^{-m}) \qquad \text{for all } m \in \mathcal M \text{ and } q^m \in E^m .
--   $$
--
--   So at a pure equilibrium of a harmonic game, every player is indifferent between *all* of their strategies. This is the key step in showing that harmonic games generically have no pure Nash equilibrium.
--
--   **Formalization Note** Pure Nash equilibrium is `AGT.IsPureNash` from the published `agt_games` bundle, which is condition (1) of the paper. $(q^m, p^{-m})$ is `Function.update p m q`.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 23, Lemma 5.1, equation (32)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_GenericPure_Games

namespace HarmonicGames.GenericPure

/-- **Lemma 5.1** (p. 23). Let `u` be a harmonic game (`u ∈ H ⊕ N`) and `p` a pure Nash
equilibrium of `u`. Then every player is indifferent between all of their strategies at `p`:
`u^m(p^m, p^{-m}) = u^m(q^m, p^{-m})` for all `m` and `q^m ∈ E^m`. -/
theorem lemma_5_1 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hu : IsHarmonicGame E u) (p : ∀ m, E m)
    (hp : AGT.IsPureNash (payoff E u) p) :
    ∀ (m : ι) (q : E m), payoff E u m p = payoff E u m (Function.update p m q) := by sorry

end HarmonicGames.GenericPure
