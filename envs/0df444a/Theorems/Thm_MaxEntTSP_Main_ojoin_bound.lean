-- Prove2me | Theorems.Thm_MaxEntTSP_Main_ojoin_bound
-- name    : MaxEntTSP.Main.ojoin_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:11.816242+00:00
-- url     : https://prove2.me/theorems/d93b2edb-57d8-4dbc-a35a-4dbddcdd0156
-- title:
--   Proof of Theorem 1.1 — expected O-join matching bound
-- statement:
--   For an optimal Held–Karp solution on a metric TSP instance, split any city and draw a tree from the exact maximum-entropy law. Set $\varepsilon_P=3.12\cdot10^{-16}$, $\eta=\varepsilon_P/1308$, and $\beta=\eta/4.1$. The minimum-cost matching $M_T$ on the tree's odd-degree vertices obeys
--   $$\mathbb E[c(M_T)]\le\left(\tfrac12-\tfrac16\varepsilon_P\beta\right)\operatorname{OPT}.$$
--
--   This is the cost improvement from the random slack and $O$-join analysis. The distinguished edge is assigned finite LP value $y_{e_0}=1$ in place of the proof's $\infty$; it has zero cost and satisfies every cut containing it.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, pp. 18–19 (PDF 20–21), proof of Theorem 1.1, displayed O-join cost bound and equations (8)–(9)

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- The matching bound derived in the proof of Theorem 1.1, pp. 18–19. -/
theorem ojoin_bound (n : ℕ) (hn : 3 ≤ n)
    (c x : Fin n → Fin n → ℝ) (hc : IsMetricCost c) (hx : IsHeldKarp x)
    (hopt : (1 / 2) * (∑ i, ∑ j, c i j * x i j) = hkValue c)
    (u : Fin n) (μ : Finset (Sym2 (Fin (n + 1))) → ℝ)
    (hμ : IsMaxEntropy (lpSupport (splitLP x u) (u0 u) (v0 n)) (splitLP x u) μ) :
    let β : ℝ := (312 / 10 ^ 18) * 10 / (1308 * 41)
    (∑ T, μ T * minMatchCost (splitCost c u) T) ≤
      (1 / 2 - (312 / 10 ^ 18 : ℝ) * β / 6) * tspOpt c := by sorry

end MaxEntTSP.Main
