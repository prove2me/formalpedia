-- Prove2me | Theorems.Thm_MaxPressure_StrictLeontief_truncation_feasible
-- name    : MaxPressure.StrictLeontief.truncation_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:56:09.115987+00:00
-- url     : https://prove2.me/theorems/31fe3217-aa55-4fc9-be64-d2180f94cdfa
-- title:
--   §6.1, proof of Theorem 6, p. 204 — the truncated allocation ã is feasible and z′Rã ≥ z′Râ
-- statement:
--   Consider a strict Leontief network satisfying the standing assumptions of §2, a buffer-level vector $z\in\mathbb R^I_+$, and let $\mathcal J_0$ be the set of service activities $j$ with $z_{i(j)}=0$. For an allocation $\hat a\in\mathcal A$ define
--   $$\tilde a_j=\begin{cases}0,& j\in\mathcal J_0,\\ \hat a_j,& j\notin\mathcal J_0.\end{cases}$$
--   Then $\tilde a\in\mathcal A$ and
--   $$z'R\tilde a\ \ge\ z'R\hat a.$$
--
--   Switching off the activities whose buffer is empty keeps every processor constraint (input activities are untouched) and does not lower the network pressure.
--
--   **Formalization Note** $\tilde a$ is `truncate N z â`, the indicator of the complement of $\mathcal J_0$ applied to $\hat a$.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 204, §6.1, proof of Theorem 6, definition of ã and the two displays following it

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

namespace MaxPressure.StrictLeontief

/-- Proof of Theorem 6, p. 204: for `z ∈ ℝ^I_+` and an allocation `â ∈ 𝒜`, the allocation
`ã` obtained by setting the coordinates in `𝒥₀` to zero is again in `𝒜`, and
`z′Rã ≥ z′Râ`. -/
theorem truncation_feasible {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (a : Fin J → ℝ) (ha : a ∈ allocSet N) :
    truncate N z a ∈ allocSet N ∧ pressure N a z ≤ pressure N (truncate N z a) z := by sorry

end MaxPressure.StrictLeontief
