-- Prove2me | Theorems.Thm_HarmonicGames_UniformMixed_proposition_5_2
-- name    : HarmonicGames.UniformMixed.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:45:57.716147+00:00
-- url     : https://prove2.me/theorems/1fab1135-a80d-48f4-9611-cfe9b3edd0d9
-- title:
--   Proposition 5.2 — correlated equilibria of normalized harmonic games are characterized by equalities
-- statement:
--   Let $G$ be a finite game with players $\mathcal M$, nonempty finite strategy sets $E^m$ and utilities $u = (u^m)_m$, and suppose $G$ is a **normalized harmonic game**, i.e. $u \in \mathcal H$ (Definition 4.2). Let $x \in \Delta E$ be a probability distribution on the set $E$ of strategy profiles, and write $x(p^m, p^{-m})$ for the probability of the profile $(p^m, p^{-m})$. The following are equivalent:
--
--   1. $x$ is a **correlated equilibrium**: for all $m$ and $p^m, q^m \in E^m$, $\sum_{p^{-m}} \big(u^m(p^m,p^{-m}) - u^m(q^m,p^{-m})\big)\, x(p^m,p^{-m}) \ge 0$ (Definition 5.1.2).
--   2. For all $m \in \mathcal M$ and $p^m, q^m \in E^m$,
--   $$
--   \sum_{p^{-m}} \big(u^m(p^m,p^{-m}) - u^m(q^m,p^{-m})\big)\, x(p^m,p^{-m}) = 0 \qquad (36).
--   $$
--   3. For all $m \in \mathcal M$ and $p^m, q^m \in E^m$,
--   $$
--   \sum_{p^{-m}} u^m(q^m,p^{-m})\, x(p^m,p^{-m}) = 0 \qquad (37).
--   $$
--
--   So in a normalized harmonic game the correlated equilibria are the points of the probability simplex lying in a linear subspace determined by the utilities.
--
--   **Formalization Note** Correlated equilibrium is the referenced `HartSchmeidler.Finite.IsCorrelatedEq`, which states Definition 5.1.2 with the sum over $p^{-m}$ written as a sum over the profiles $p$ with $p^m$ fixed; the same convention is used for (36) and (37). The equivalence of the three conditions is stated as (i) ⇔ (ii) and (ii) ⇔ (iii).
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 25, Proposition 5.2, (36), (37)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HartSchmeidler_Finite_Game
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games

namespace HarmonicGames.UniformMixed

/-- **Proposition 5.2** (p. 25): let `u ∈ H` be a normalized harmonic game and `x ∈ ΔE` a
probability distribution on strategy profiles.  The following are equivalent:
(i) `x` is a correlated equilibrium (Definition 5.1.2);
(ii) for all `m` and `p^m, q^m ∈ E^m`,
`∑_{p^{-m}} (u^m(p^m, p^{-m}) - u^m(q^m, p^{-m})) x(p^m, p^{-m}) = 0` (36);
(iii) for all `m` and `p^m, q^m ∈ E^m`, `∑_{p^{-m}} u^m(q^m, p^{-m}) x(p^m, p^{-m}) = 0` (37).
Sums over `p^{-m}` are sums over the profiles `p` with `p m = a` (here `a = p^m`, `b = q^m`). -/
theorem proposition_5_2 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u : HarmonicGames.Decomposition.Games E) (hu : u ∈ HarmonicGames.Decomposition.harmonicSubspace E) (x : (∀ k, E k) → ℝ) (hx : AGT.IsLottery x) :
    (HartSchmeidler.Finite.IsCorrelatedEq (HarmonicGames.GenericPure.payoff E u) x ↔
      ∀ (m : ι) (a b : E m),
        ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
          (HarmonicGames.GenericPure.payoff E u m p - HarmonicGames.GenericPure.payoff E u m (Function.update p m b)) * x p = 0) ∧
    ((∀ (m : ι) (a b : E m),
        ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
          (HarmonicGames.GenericPure.payoff E u m p - HarmonicGames.GenericPure.payoff E u m (Function.update p m b)) * x p = 0) ↔
      ∀ (m : ι) (a b : E m),
        ∑ p ∈ Finset.univ.filter (fun p : ∀ k, E k => p m = a),
          HarmonicGames.GenericPure.payoff E u m (Function.update p m b) * x p = 0) := by sorry

end HarmonicGames.UniformMixed
