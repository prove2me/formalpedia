-- Prove2me | Theorems.Thm_LNChannels_Exact_theorem_1_i_cost
-- name    : LNChannels.Exact.theorem_1_i_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:07.853169+00:00
-- url     : https://prove2.me/theorems/b4a31e75-685b-4ad5-ad71-2807406cda15
-- title:
--   Theorem 1 (i), (1), p. 6 — the cost of a unidirectional channel
-- statement:
--   Let only node 2 pay, at rate $\lambda_2>0$, let $r>0$, $B\in\mathbb R$, and let $l_2\ge1$ be the natural size of the unidirectional channel. The unidirectional cost system ($J(n)=l_2\frac{r}{r+\lambda_2}+J(n+1)\frac{\lambda_2}{r+\lambda_2}$ for $0\le n<l_2$, with $J(l_2)=J(0)+B$) has a solution, and every solution has
--
--   $$c^{0,l_2}(0,\lambda_2)=J(0)=l_2+B\left(\left(\frac{r+\lambda_2}{\lambda_2}\right)^{l_2}-1\right)^{-1}.$$
--
--   This is the cost of settling a one-directional stream through a channel, the benchmark against which both on-chain settlement and bidirectional channels are compared.
--
--   **Formalization Note** The cost is defined by its equations (`IsUniCostFn`), not by (1). The size is a natural number and the power is a natural power.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 6 (PDF p. 7), Theorem 1 (i), equation (1); proof in §5.2, pp. 10–11

import Mathlib
import Definitions.Def_LNChannels_Exact_IsUniCostFn

set_option autoImplicit false

namespace LNChannels.Exact

/-- Theorem 1 (i), (1), p. 6 (proof in §5.2, pp. 10–11): the cost `c^{0,l₂}(0, λ₂) = J(0)` of a
unidirectional channel of size `l₂`. The cost system of §5.2 has a solution, and every solution
has `J(0) = l₂ + B(((r + λ₂)/λ₂)^{l₂} − 1)⁻¹`. -/
theorem theorem_1_i_cost (lam₂ r B : ℝ) (l₂ : ℕ)
    (hlam₂ : 0 < lam₂) (hr : 0 < r) (hl₂ : 1 ≤ l₂) :
    (∃ J : ℤ → ℝ, IsUniCostFn lam₂ r B l₂ J) ∧
    ∀ J : ℤ → ℝ, IsUniCostFn lam₂ r B l₂ J →
      J 0 = (l₂ : ℝ) + B * (((r + lam₂) / lam₂) ^ l₂ - 1)⁻¹ := by sorry

end LNChannels.Exact
