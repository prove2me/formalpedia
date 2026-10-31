-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_proposition_3_1_value
-- name    : HubSpokePricing.Lagrangian.proposition_3_1_value
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T19:22:22.919993+00:00
-- url     : https://prove2.me/theorems/664af381-3018-4376-af90-3f5715899240
-- title:
--   Proposition 3.1 (decomposition (4)), pp. 11–12 — the relaxation value is V̄^λ = mλ + Σᵢ h_i^λ from every initial state
-- statement:
--   Let $N$ be a hub-and-spoke network satisfying the standing assumptions (Assumption 2.1): one hub, $n\ge1$ spokes, $m$ resources, request probabilities $q_{i0},q_{0i}>0$ summing to one, and revenue functions $r_{i0},r_{0i}$ on $[0,1]$. Fix a dual variable $\lambda\ge0$.
--
--   Consider the Lagrangian relaxation (3). In it, the hub's non-negativity constraint is dropped, each spoke level stays in $[0:m]$, and each period earns its revenue plus the Lagrangian reward $\lambda\big(m-\sum_i x_{i,t}\big)$. Let $\bar V^\lambda_{(3)}(x^0)$ be its optimal long-run average value from the initial spoke levels $x^0\in\bar{\mathcal X}=\{x\in\mathbb N^n:x_i\le m\ \forall i\}$. Then this value does not depend on $x^0$ and decomposes over spokes:
--   $$\bar V^\lambda_{(3)}(x^0)=m\lambda+\sum_{i=1}^n h_i^\lambda\qquad\text{for all }x^0\in\bar{\mathcal X},\tag{4}$$
--   where $h_i^\lambda$ is the optimal value of the spoke problem (6).
--
--   This is the decomposition part of Proposition 3.1. The other part, the bound $V^{\mathrm{OPT}}\le\bar V^\lambda$, is a weak-duality argument. Together they make $\bar V^\lambda=m\lambda+\sum_ih_i^\lambda$ a computable upper bound on the optimal revenue for every $\lambda\ge0$.
--
--   **Formalization Note.** `VbarRelax N lam x0` is the supremum, over deterministic history-dependent policies feasible for (3), of the $\limsup$ of the $T$-period average of revenue plus the Lagrangian reward; the paper writes $\lim$. `Vbar N lam` is $m\lambda+\sum_ih_i^\lambda$, where $h_i^\lambda$ is the optimal value of (6). The paper defines $h_i^\lambda$ as the spoke DP's optimal average revenue and identifies the two in Proposition 3.2. This statement is the first conjunct of the milestone `proposition_3_1`.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, pp. 11–12, Proposition 3.1, relaxation (3) and decomposition (4); spoke problem (6) and Proposition 3.2, p. 12

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Proposition 3.1, decomposition (4) (pp. 11–12): for every `λ ≥ 0` the optimal average value
`V̄^λ` of the Lagrangian relaxation (3) is the same from every initial state in `𝒳̄` and equals
`mλ + ∑ᵢ h_i^λ`, with `h_i^λ` the optimal value of the spoke problem (6) (Proposition 3.2). -/
theorem proposition_3_1_value (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ x0 : Fin N.n → ℕ, InXbar N x0 → VbarRelax N lam x0 = Vbar N lam := by sorry

end HubSpokePricing.Lagrangian
