-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_theorem_7_6_4
-- name    : MDPFinance.InfiniteHorizonApplications.theorem_7_6_4
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:18.687283+00:00
-- url     : https://prove2.me/theorems/d2fa9106-d495-4031-9cd1-c0954d83475c
-- title:
--   Theorem 7.6.4 — in a fair game every non-degenerate strategy is optimal
-- statement:
--   At exactly $p=1/2$ the wealth process is a martingale, so the maximal probability of reaching $B$
--   is simply the fair-odds value $x/B$ — and, strikingly, *every* stationary strategy that bets a
--   positive amount whenever it can (not merely the timid or bold strategy specifically) achieves this
--   same optimal value: with no edge either way, how one bets does not matter, only that one keeps
--   playing.
--
--   **Moderation note.** Optimality is now among all Markov policies (the draft's $J_\infty$ ranged over stationary rules only).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 229, Theorem 7.6.4

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Casino

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Theorem 7.6.4 (Bäuerle–Rieder, p. 229, PDF 240). If `p = 1/2`, then the maximal probability
that the player will reach `B` before going bankrupt is given by `J_\infty(x) = x/B`, `x \in E`,
and every stationary strategy `(f,f,\dots)` with `f(x) > 0` for `x > 0` is optimal. -/
theorem theorem_7_6_4 (Mk : CasinoMarket) (hp : Mk.p = 1 / 2) :
    (∀ x : Fin (Mk.B + 1), Mk.Jinf x = (x.1 : ℝ) / Mk.B) ∧
      ∀ f : Fin (Mk.B + 1) → ℕ, (∀ x : Fin (Mk.B + 1), 0 < x.1 → 0 < f x) →
        ∀ x, Mk.Jinfpi f x = Mk.Jinf x := by sorry

end MDPFinance.InfiniteHorizonApplications
