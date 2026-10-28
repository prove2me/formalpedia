-- Prove2me | Theorems.Thm_MaxEntTSP_Main_fact_2_2
-- name    : MaxEntTSP.Main.fact_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:16.341568+00:00
-- url     : https://prove2.me/theorems/608e4ba5-4d7a-4b32-8b82-6aeaa6f48475
-- title:
--   Fact 2.2 — expected tree cost equals the cost of its marginals
-- statement:
--   Suppose $e_0$ has zero metric cost and $\mu$ is any distribution on spanning trees of $E$ with edge marginals $x$. Then
--   $$\mathbb E_{T\sim\mu}\bigl[c(T\cup\{e_0\})\bigr]=\sum_{e\in E}c_e x_e.$$
--
--   The identity is linear in the edge indicators and does not require maximum entropy.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, p. 6 (PDF 8), Fact 2.2

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- Linear expectation equals the cost of the marginal vector. -/
theorem fact_2_2 (m : ℕ) (x c : Fin m → Fin m → ℝ)
    (hc : IsMetricCost c) (a b : Fin m) (hab : a ≠ b) (hcost0 : c a b = 0)
    (μ : Finset (Sym2 (Fin m)) → ℝ)
    (hμ : IsTreeDistribution (lpSupport x a b) x μ) :
    (∑ T, μ T * treeCost c (insert (s(a, b)) T)) =
      ∑ e ∈ lpSupport x a b, pairCost c e * pairCost x e := by sorry

end MaxEntTSP.Main
