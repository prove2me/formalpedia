-- Prove2me | Theorems.Thm_OptHedgeGames_Supplement_theorem_3_3
-- name    : OptHedgeGames.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:21:20.678253+00:00
-- url     : https://prove2.me/theorems/629f2972-2129-47ed-845f-5434e364eef7
-- title:
--   Theorem 3.3 — with $\eta\le1/(8704\sqrt m\log T)$ every player of an $m$-player game has regret at most $\log n/\eta+68\eta\log T$
-- statement:
--   Let $T\ge2$, and let all $m$ players of a game $G\in\mathcal G(m,n)$ (losses in $[0,1]$, $n$ actions each) run Optimistic Hedge with a common learning rate $\eta$ satisfying
--   $$
--   0<\eta\le\frac1{8704\sqrt m\,\log T}.
--   $$
--   Then every player $i$ has regret
--   $$
--   \mathrm{Reg}_i(T)\le\frac{\log n}{\eta}+68\,\eta\log T.
--   $$
--   In particular, at $\eta=1/(8704\sqrt m\log T)$ every player's regret is $O(\sqrt m\,\log n\,\log T)$: there is an absolute constant $C$ such that $\mathrm{Reg}_i(T)\le C\sqrt m\log n\log T$ for every $m,n\ge1$, every game, every $T\ge2$ and every player $i$.
--
--   This is the polylogarithmic regret bound of the paper for any number of players, with explicit constants; the horizon $T$ enters the learning rate.
--
--   **Formalization Note** $\log$ is the natural logarithm. Both clauses are stated for every player.
--
--   Differences from the source:
--   - encoding: "with n actions for player i" → every player has the same $n$ actions; reason: the paper assumes a common $n$ (footnote 1, p.4), and $\mathcal G(m,n)$ is defined that way.
--   - reading: "regret at most $O(\sqrt m\log n\log T)$" → one absolute constant $C$, chosen before $m$, $n$, the game and $T$; reason: the paper's constants are absolute; this is the reading of $O(\cdot)$ used for the mission's goal.
--   - encoding: an $m$-player game with $n$ actions → $1\le m$, $1\le n$ explicit, players and actions 0-based (`Fin m`, `Fin n`); reason: a game has at least one player and one action, and the minimum in the regret needs $n\ge1$.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Theorem 3.3, p.6

import Mathlib
import Definitions.Def_OptHedgeGames_Supplement_MultiRun

namespace OptHedgeGames

namespace Supplement

/-- **Theorem 3.3 (Logarithmic regret for `m` players).** Let `T ≥ 2`. If all players of an
`m`-player game with `n` actions run Optimistic Hedge with learning rate
`0 < η ≤ 1/(8704√m log T)`, then every player's regret satisfies
`Regᵢ(T) ≤ log n/η + 68η log T`. In particular, for `η = 1/(8704√m log T)` every player achieves
regret at most `O(√m log n log T)`
(Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Theorem 3.3, p.6).

**Formalization Note** `log` is `Real.log` (natural logarithm). The games are `MGame m n` (losses in
`[0, 1]`, all players with the same `n` actions), and `Regᵢ(T)` is `G.Reg η i T`. The `O(·)` of the
second clause is read as one absolute constant `C`, chosen before `m`, `n`, the game and `T`. -/
theorem theorem_3_3 :
    (∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → ∀ (G : MGame m n) (T : ℕ), 2 ≤ T → ∀ η : ℝ, 0 < η →
      η ≤ 1 / (8704 * Real.sqrt (m : ℝ) * Real.log (T : ℝ)) → ∀ i : Fin m,
        G.Reg η i T ≤ Real.log (n : ℝ) / η + 68 * η * Real.log (T : ℝ)) ∧
    (∃ C : ℝ, ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → ∀ (G : MGame m n) (T : ℕ), 2 ≤ T → ∀ i : Fin m,
      G.Reg (1 / (8704 * Real.sqrt (m : ℝ) * Real.log (T : ℝ))) i T ≤
        C * (Real.sqrt (m : ℝ) * Real.log (n : ℝ) * Real.log (T : ℝ))) := by sorry

end Supplement

end OptHedgeGames
