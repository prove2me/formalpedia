-- Prove2me | Theorems.Thm_OptHedgeGames_theorem_3_4
-- name    : OptHedgeGames.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:57.003799+00:00
-- url     : https://prove2.me/theorems/35f1df2f-25d1-4e22-8775-0a6c0d040250
-- title:
--   Theorem 3.4 — two players running Optimistic Hedge with $\eta\le c/n$ have regret at most $\log n/\eta+\eta$
-- statement:
--   There is an absolute constant $c>0$ with the following properties. In every two-player game with loss matrices $A,B\in[0,1]^{n\times n}$, for every learning rate $0<\eta\le c/n$ and every horizon $T\ge1$, if both players run Optimistic Hedge with learning rate $\eta$, then the regret of each player $i$ is bounded by
--   $$
--   \mathrm{Reg}_i(T)\le\frac{\log n}{\eta}+\eta.
--   $$
--   In particular, for $\eta=c/n$, both players have regret $O(n\log n)$ for all $T$: there is an absolute constant $C$ with $\mathrm{Reg}_i(T)\le C\,n\log n$ for all $n$, all games and all $T$.
--
--   This gives a horizon-independent regret bound for fixed-rate Optimistic Hedge in general-sum two-player games, with an explicit polynomial dependence on the number of actions.
--
--   Differences from the source:
--   - reading: O(n log n) for all T → ∃ C, uniform in n ≥ 1, the game and T, with the same c; reason: the standard reading of an absolute O(·); for n ≥ 2 it follows from the first clause with C = 1/c + c, and at n = 1 both sides are 0
--   - encoding: G ∈ G(2, n) → Game n: two matrices with entries in [0,1]; reason: (1) at m = 2 with the Setup of §3.3, p.7
--   - encoding: n with no stated bound → 1 ≤ n; reason: no strategy exists at n = 0
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Theorem 3.4, p.7

import Mathlib
import Definitions.Def_OptHedgeGames_TwoPlayerRun

namespace OptHedgeGames

/-- **Theorem 3.4** (constant regret for two players; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Theorem 3.4, p.7). There is an absolute
constant `c > 0` such that in every two-player game `G ∈ G(2, n)`, for every learning rate
`0 < η ≤ c/n` and every horizon `T ≥ 1`, if both players run Optimistic Hedge with learning rate `η`,
then the regret of each player is bounded by `Regᵢ(T) ≤ log n/η + η`. In particular, for `η = c/n`, both
players have regret `O(n log n)` for all `T`.

**Formalization Note** The first clause holds for both players; `Real.log` is the natural logarithm.
`c` comes before `n`, the game, `η` and `T`. `O(n log n)` is read as: an absolute `C`, uniform in
`n ≥ 1`, the game and `T`, with the same `c`. `n ≥ 1`, since no strategy exists at `n = 0`. At `n = 1`
the regret is `0`. -/
theorem theorem_3_4 : ∃ c : ℝ, 0 < c ∧
    (∀ {n : ℕ}, 1 ≤ n → ∀ (G : Game n) (η : ℝ), 0 < η → η ≤ c / (n : ℝ) → ∀ T : ℕ, 1 ≤ T →
      reg (G.x1 η) (G.l1 η) T ≤ Real.log (n : ℝ) / η + η ∧
        reg (G.x2 η) (G.l2 η) T ≤ Real.log (n : ℝ) / η + η) ∧
    (∃ C : ℝ, ∀ {n : ℕ}, 1 ≤ n → ∀ (G : Game n) (T : ℕ), 1 ≤ T →
      reg (G.x1 (c / (n : ℝ))) (G.l1 (c / (n : ℝ))) T ≤ C * ((n : ℝ) * Real.log (n : ℝ)) ∧
        reg (G.x2 (c / (n : ℝ))) (G.l2 (c / (n : ℝ))) T ≤ C * ((n : ℝ) * Real.log (n : ℝ))) := by sorry

end OptHedgeGames
