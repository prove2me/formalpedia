-- Prove2me | Theorems.Thm_LNChannels_Exact_cost_function
-- name    : LNChannels.Exact.cost_function
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:16.871152+00:00
-- url     : https://prove2.me/theorems/d2ebb621-e814-4981-a564-eb48f35f1542
-- title:
--   §5.1, p. 10 — the cost function $J(n)$ of a bidirectional channel in closed form
-- statement:
--   Let $0<\lambda_1\le\lambda_2$, $r>0$, $B\in\mathbb R$, and natural commitments $l_1,l_2\ge1$; let $\alpha_\pm$ be the roots (4). The bidirectional cost system ((15) with $J(-l_1)=J(+l_2)=J(0)+B$) has a solution, and every solution satisfies, at every balance $-l_1\le n\le l_2$,
--
--   $$J(n)=l_1+l_2-B\,\frac{(\alpha_-^{l_1+l_2}-1)\,\alpha_+^{l_1+n}-(\alpha_+^{l_1+l_2}-1)\,\alpha_-^{l_1+n}}{\alpha_-^{l_1}-\alpha_+^{l_1}+(\alpha_+^{l_1}-1)\,\alpha_-^{l_1+l_2}-(\alpha_-^{l_1}-1)\,\alpha_+^{l_1+l_2}}.$$
--
--   At $n=0$ this is the closed form (3) of the channel's cost.
--
--   **Formalization Note** The paper prints the exponent of the numerator's $\alpha_\pm$ as $l+n$; it is $l_1+n$ (this is what solving the two boundary equations gives, and what reduces to (3) at $n=0$). The powers $\alpha_\pm^{l_1+n}$ are integer powers (`zpow`), with a nonnegative exponent on the lattice. Existence of a solution is part of the statement.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 10 (PDF p. 11), §5.1, display after "which yield the cost function" (exponent l + n read as l1 + n)

import Mathlib
import Definitions.Def_LNChannels_Exact_alphaPlus
import Definitions.Def_LNChannels_Exact_alphaMinus
import Definitions.Def_LNChannels_Exact_IsBiCostFn

set_option autoImplicit false

namespace LNChannels.Exact

/-- §5.1, p. 10, the display after "which yield the cost function": the cost `J(n)` at every
balance `−l₁ ≤ n ≤ l₂` of a bidirectional channel. The printed exponent `l + n` in the numerator
is read as `l₁ + n`. Powers with exponent depending on `n` are `zpow`s with exponent
`l₁ + n ≥ 0` on the lattice. -/
theorem cost_function (lam₁ lam₂ r B : ℝ) (l₁ l₂ : ℕ)
    (hlam₁ : 0 < lam₁) (hlam : lam₁ ≤ lam₂) (hr : 0 < r) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) :
    let a := alphaMinus lam₁ lam₂ r
    let b := alphaPlus lam₁ lam₂ r
    (∃ J : ℤ → ℝ, IsBiCostFn lam₁ lam₂ r B l₁ l₂ J) ∧
    ∀ J : ℤ → ℝ, IsBiCostFn lam₁ lam₂ r B l₁ l₂ J →
      ∀ n : ℤ, -(l₁ : ℤ) ≤ n → n ≤ (l₂ : ℤ) →
        J n = (l₁ : ℝ) + l₂ - B *
          (((a ^ (l₁ + l₂) - 1) * b ^ ((l₁ : ℤ) + n) - (b ^ (l₁ + l₂) - 1) * a ^ ((l₁ : ℤ) + n)) /
            (a ^ l₁ - b ^ l₁ + (b ^ l₁ - 1) * a ^ (l₁ + l₂) - (a ^ l₁ - 1) * b ^ (l₁ + l₂))) := by sorry

end LNChannels.Exact
