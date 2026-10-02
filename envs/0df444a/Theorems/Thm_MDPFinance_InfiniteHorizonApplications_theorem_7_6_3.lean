-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_theorem_7_6_3
-- name    : MDPFinance.InfiniteHorizonApplications.theorem_7_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:11.634817+00:00
-- url     : https://prove2.me/theorems/f77e23ae-77f9-4adc-bdae-10d7531abc44
-- title:
--   Theorem 7.6.3 — the bold strategy is optimal in an unfavorable game
-- statement:
--   When the win probability is at most $1/2$, betting everything needed to reach $B$ in the fewest
--   possible steps (the bold strategy) is optimal: the game is unfavorable, so minimizing the number
--   of bets — rather than grinding out a long sequence of small ones — maximizes the chance of
--   reaching the target before ruin.
--
--   **Moderation note.** Optimality is now among all Markov policies (the draft's $J_\infty$ ranged over stationary rules only).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 228, Theorem 7.6.3

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Casino

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Theorem 7.6.3 (Bäuerle–Rieder, p. 228, PDF 239). If `p \le 1/2`, the bold strategy is
optimal, i.e. it maximizes the probability that the player will reach `B` before going bankrupt. -/
theorem theorem_7_6_3 (Mk : CasinoMarket) (hp : Mk.p ≤ 1 / 2) :
    ∀ x, Mk.Jinfpi Mk.bold x = Mk.Jinf x := by sorry

end MDPFinance.InfiniteHorizonApplications
