-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_theorem_7_6_2
-- name    : MDPFinance.InfiniteHorizonApplications.theorem_7_6_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:07.419005+00:00
-- url     : https://prove2.me/theorems/b3396b3d-2b5d-4a4b-ad75-09a4369f69e3
-- title:
--   Theorem 7.6.2 — the timid strategy is optimal in a favorable game
-- statement:
--   When the win probability is at least $1/2$, betting the minimum amount every time (the timid
--   strategy) is the best possible strategy for reaching the target fortune $B$: patience, together
--   with the law of large numbers working in the gambler's favor, beats any bolder alternative.
--
--   **Moderation note.** Optimality is now among all Markov policies (the draft's $J_\infty$ ranged over stationary rules only).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 227, Theorem 7.6.2

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Casino

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Theorem 7.6.2 (Bäuerle–Rieder, p. 227, PDF 238). If `p \ge 1/2`, the timid strategy is
optimal, i.e. it maximizes the probability that the player will reach `B` before going bankrupt. -/
theorem theorem_7_6_2 (Mk : CasinoMarket) (hp : 1 / 2 ≤ Mk.p) :
    ∀ x, Mk.Jinfpi Mk.timid x = Mk.Jinf x := by sorry

end MDPFinance.InfiniteHorizonApplications
