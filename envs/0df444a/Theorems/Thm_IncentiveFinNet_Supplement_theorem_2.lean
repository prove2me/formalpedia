-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_theorem_2
-- name    : IncentiveFinNet.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:31:54.170545+00:00
-- url     : https://prove2.me/theorems/5b50712a-bb23-5c60-ab14-3d63072fbcc4
-- title:
--   Theorem 2 — stable points cannot be dominated
-- statement:
--   Let $(W,P)$ be a stable point of a network setting (Definition 3). Then no feasible $(W',P')$ dominates $(W,P)$: there is no feasible $(W',P')$ with
--
--   $$
--   g_i(W,P)\le g_i(W',P')\ \text{ for all } i\in[n]\quad\text{and}\quad g_k(W,P)<g_k(W',P')\ \text{ for some } k .
--   $$
--
--   Here $g_i$ is the mean-variance utility (1) and feasibility is Definition 2. The result holds for every network setting: any number of agents, individual covariances $\Sigma_i$, and any symmetric pattern of permitted edges.
--
--   The stable point is therefore Pareto optimal among feasible networks and prices: no reallocation of contracts and prices makes every agent at least as well off and one strictly better off.
--
--   Differences from the source: none.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 2, p.12; restated and proved in A.5, pp.36–37

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable
import Definitions.Def_IncentiveFinNet_Supplement_Dominates

open Matrix

namespace IncentiveFinNet.Supplement

/-- **Theorem 2 (Stable points cannot be dominated)**, Jalan, Chakrabarti, Sarkar,
*Incentive-Aware Models of Financial Networks*, arXiv:2212.06808v3, p.12 (restated in A.5,
p.36): "Suppose a stable point `(W, P)` exists. Then, there is no feasible `(W′, P′)` that
dominates `(W, P)`."

Stated for every network setting and every stable point `(W, P)` (Definition 3); domination is
`Dominates` (p.12). -/
theorem theorem_2 {n : ℕ} (S : NetworkSetting n) (W P : Matrix (Fin n) (Fin n) ℝ)
    (h : Stable S W P) :
    ¬ ∃ W' P' : Matrix (Fin n) (Fin n) ℝ, Feasible S W' P' ∧ Dominates S W' P' W P := by sorry

end IncentiveFinNet.Supplement
