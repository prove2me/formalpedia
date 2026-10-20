-- Prove2me | Theorems.Thm_LNChannels_Exact_theorem_1_ii
-- name    : LNChannels.Exact.theorem_1_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:24.917303+00:00
-- url     : https://prove2.me/theorems/74b8604d-95aa-46b0-b4f4-c1c61aed0c7c
-- title:
--   Theorem 1 (ii), (3)–(4), p. 6 — the cost of a bidirectional channel in closed form
-- statement:
--   Node 1 pays node 2 at rate $\lambda_1$ and node 2 pays node 1 at rate $\lambda_2$ (independent Poisson streams of unit payments), with $0<\lambda_1\le\lambda_2$; capital is discounted at rate $r>0$, a reset costs $B\in\mathbb R$, and the nodes commit natural amounts $l_1,l_2\ge1$. Let $\alpha_\pm$ be the roots (4),
--
--   $$\alpha_\pm=\frac{\lambda_1+\lambda_2+r\pm\sqrt{(\lambda_2-\lambda_1)^2+r^2+2r(\lambda_2+\lambda_1)}}{2\lambda_2}.$$
--
--   The bidirectional cost system ((15) on $-l_1<n<l_2$ with $J(-l_1)=J(+l_2)=J(0)+B$) has a solution, and for every solution the cost of the channel $c^{l_1,l_2}(\lambda_1,\lambda_2)=J(0)$ equals
--
--   $$c^{l_1,l_2}(\lambda_1,\lambda_2)=l_1+l_2-B\,\frac{\alpha_-^{l_1}(1-\alpha_+^{l_1+l_2})-\alpha_+^{l_1}(1-\alpha_-^{l_1+l_2})}{\alpha_-^{l_1}(1-\alpha_+^{l_1+l_2})-\alpha_+^{l_1}(1-\alpha_-^{l_1+l_2})+\alpha_+^{l_1+l_2}-\alpha_-^{l_1+l_2}}.$$
--
--   This closed form is the basis of every comparison in the paper between bidirectional channels, unidirectional channels and on-chain settlement.
--
--   **Formalization Note** The cost is defined by the first-step equation and the reset conditions (`IsBiCostFn`), never by (3); the statement asserts both existence of a solution and the value of $J(0)$ for every solution. Sizes are natural numbers and powers are natural powers; at natural sizes this is the same number as the real-exponent expression used for minimizations over real sizes. The paper's normalization $\lambda_1\le\lambda_2$ is kept although the formula does not need it. No sign of $B$ is assumed.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 6 (PDF p. 7), Theorem 1 (ii), equations (3)–(4); proof §5, §5.1, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_LNChannels_Exact_alphaPlus
import Definitions.Def_LNChannels_Exact_alphaMinus
import Definitions.Def_LNChannels_Exact_IsBiCostFn

set_option autoImplicit false

namespace LNChannels.Exact

/-- Theorem 1 (ii), (3)–(4), p. 6: the cost `c^{l₁,l₂}(λ₁, λ₂) = J(0)` of a bidirectional channel
in closed form. The cost system (15) with the reset conditions of §5.1 has a solution, and every
solution has `J(0)` equal to (3), with `α±` from (4). -/
theorem theorem_1_ii (lam₁ lam₂ r B : ℝ) (l₁ l₂ : ℕ)
    (hlam₁ : 0 < lam₁) (hlam : lam₁ ≤ lam₂) (hr : 0 < r) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) :
    let a := alphaMinus lam₁ lam₂ r
    let b := alphaPlus lam₁ lam₂ r
    (∃ J : ℤ → ℝ, IsBiCostFn lam₁ lam₂ r B l₁ l₂ J) ∧
    ∀ J : ℤ → ℝ, IsBiCostFn lam₁ lam₂ r B l₁ l₂ J →
      J 0 = (l₁ : ℝ) + l₂ - B *
        ((a ^ l₁ * (1 - b ^ (l₁ + l₂)) - b ^ l₁ * (1 - a ^ (l₁ + l₂))) /
          (a ^ l₁ * (1 - b ^ (l₁ + l₂)) - b ^ l₁ * (1 - a ^ (l₁ + l₂))
            + b ^ (l₁ + l₂) - a ^ (l₁ + l₂))) := by sorry

end LNChannels.Exact
