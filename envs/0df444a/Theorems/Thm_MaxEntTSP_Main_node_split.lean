-- Prove2me | Theorems.Thm_MaxEntTSP_Main_node_split
-- name    : MaxEntTSP.Main.node_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:06.824285+00:00
-- url     : https://prove2.me/theorems/c45bf99f-ec89-43b5-b466-1a2f33a2ff27
-- title:
--   §1.1, p. 2 — splitting a city preserves the TSP and LP costs
-- statement:
--   Let $c$ be metric costs on $n\ge3$ cities and let $x$ be an optimal Held–Karp solution. For any city $u$, split it into $u_0,v_0$, divide the mass of each incident LP edge equally between the copies, and insert the edge $e_0=\{u_0,v_0\}$ with LP value $1$ and cost $0$.
--
--   The split costs remain metric, the split LP vector is feasible, its objective equals the original objective, and the optimal tour cost is unchanged:
--   $$x'_{e_0}=1,\qquad c(x')=c(x),\qquad \operatorname{OPT}(c')=\operatorname{OPT}(c).$$
--
--   This reduction provides the rooted instance used throughout the paper.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, p. 2 (PDF 4), §1.1, paragraph beginning 'Given x0'

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- The WLOG node split on p. 2 preserves the relaxation and optimum cost. -/
theorem node_split (n : ℕ) (hn : 3 ≤ n)
    (c x : Fin n → Fin n → ℝ) (hc : IsMetricCost c) (hx : IsHeldKarp x)
    (hopt : (1 / 2) * (∑ i, ∑ j, c i j * x i j) = hkValue c)
    (u : Fin n) :
    IsMetricCost (splitCost c u) ∧
    IsHeldKarp (splitLP x u) ∧
    splitLP x u (u0 u) (v0 n) = 1 ∧
    (∑ i, ∑ j, splitCost c u i j * splitLP x u i j) =
      (∑ i, ∑ j, c i j * x i j) ∧
    tspOpt (splitCost c u) = tspOpt c := by sorry

end MaxEntTSP.Main
