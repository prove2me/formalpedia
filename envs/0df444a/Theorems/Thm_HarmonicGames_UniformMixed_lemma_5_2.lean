-- Prove2me | Theorems.Thm_HarmonicGames_UniformMixed_lemma_5_2
-- name    : HarmonicGames.UniformMixed.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:45:52.173162+00:00
-- url     : https://prove2.me/theorems/a8b7cdbb-fab7-4fd0-9998-178f6e088500
-- title:
--   Lemma 5.2 — in a harmonic game, $\sum_{p^{-m}} u^m(r^m,p^{-m}) - u^m(q^m,p^{-m}) = 0$
-- statement:
--   Let $G$ be a finite game with players $\mathcal M$, nonempty finite strategy sets $E^m$ and utilities $u = (u^m)_m$, and suppose $G$ is a **harmonic game**, i.e. $u \in \mathcal H \oplus \mathcal N$, the sum of the harmonic and nonstrategic subspaces of Definition 4.2. Then for every player $m \in \mathcal M$ and all strategies $q^m, r^m \in E^m$,
--
--   $$
--   \sum_{p^{-m} \in E^{-m}} \big( u^m(r^m, p^{-m}) - u^m(q^m, p^{-m}) \big) = 0 ,
--   $$
--
--   where $E^{-m} = \prod_{k \ne m} E^k$ is the set of strategy profiles of the players other than $m$.
--
--   In words: against an opponent profile drawn uniformly at random, every player of a harmonic game is indifferent between any two of its pure strategies. This is the identity behind Theorem 5.4.
--
--   **Formalization Note** The sum over $p^{-m} \in E^{-m}$ is written as the sum over the profiles $p$ with $p^m = r^m$ (one profile per $p^{-m}$), and $(q^m, p^{-m})$ is `Function.update p m q`. Harmonic game means membership in the submodule sum $\mathcal H \sqcup \mathcal N$.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 27, Lemma 5.2 (proof in Appendix A, pp. 42–43)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games

namespace HarmonicGames.UniformMixed

/-- **Lemma 5.2** (p. 27): in a harmonic game `u ∈ H ⊕ N`, for every player `m` and all
`q^m, r^m ∈ E^m`, `∑_{p^{-m} ∈ E^{-m}} (u^m(r^m, p^{-m}) - u^m(q^m, p^{-m})) = 0`.
The sum over `p^{-m}` is the sum over the profiles `p` with `p^m = r^m`, each
`p^{-m}` counted once. -/
theorem lemma_5_2 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hu : u ∈ HarmonicGames.GenericPure.harmonicGames E) (m : ι) (q r : E m) :
    ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = r),
      (HarmonicGames.GenericPure.payoff E u m p - HarmonicGames.GenericPure.payoff E u m (Function.update p m q)) = 0 := by sorry

end HarmonicGames.UniformMixed
