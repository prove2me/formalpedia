-- Prove2me | Theorems.Thm_MaxEntTSP_Main_theorem_1_1
-- name    : MaxEntTSP.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:19.878857+00:00
-- url     : https://prove2.me/theorems/c69755bb-94cb-4c78-999c-d8b56f3e34c1
-- title:
--   Theorem 1.1 — maximum-entropy tree rounding beats 3/2 in expectation
-- statement:
--   There is one absolute $\varepsilon>10^{-36}$ such that, for every metric TSP instance on $n\ge3$ cities, every optimal Held–Karp vector $x^0$, every choice of city to split, and every maximum-entropy law $\mu$ on spanning trees with the resulting exact LP marginals, the cost of the sampled tree plus a cheapest matching on its odd-degree vertices satisfies
--   $$\mathbb E_{T\sim\mu}[c(T)+c(M_T)]\le\left(\tfrac32-\varepsilon\right)\operatorname{OPT}.$$
--
--   Shortcutting the tree-plus-matching multigraph gives a tour of no greater cost in the metric. The uniform placement of $\varepsilon$ is the improvement over the classical $3/2$ guarantee.
--
--   **Formalization Note** The statement analyzes Algorithm 1 with the exact maximum-entropy distribution. The paper's polynomial-time approximation to that distribution, and hence polynomial-time computability of the tour-producing algorithm, are not formalized here. Existence of the exact law is a separate milestone.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, p. 1 (PDF 3), Theorem 1.1; pp. 2–3 (PDF 4–5), Algorithm 1; pp. 18–19 (PDF 20–21), proof

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- Expected cost of Algorithm 1 with the exact maximum-entropy tree law. -/
theorem theorem_1_1 :
    ∃ ε : ℝ, 1 / 10 ^ 36 < ε ∧
      ∀ (n : ℕ), 3 ≤ n →
      ∀ c : Fin n → Fin n → ℝ, IsMetricCost c →
      ∀ x : Fin n → Fin n → ℝ, IsHeldKarp x →
        (1 / 2) * (∑ i, ∑ j, c i j * x i j) = hkValue c →
      ∀ (u : Fin n) (μ : Finset (Sym2 (Fin (n + 1))) → ℝ),
        IsMaxEntropy (lpSupport (splitLP x u) (u0 u) (v0 n)) (splitLP x u) μ →
        algCost (splitCost c u) μ ≤ (3 / 2 - ε) * tspOpt c := by sorry

end MaxEntTSP.Main
