-- Prove2me | Theorems.Thm_LNChannels_Exact_general_solution
-- name    : LNChannels.Exact.general_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:13.461989+00:00
-- url     : https://prove2.me/theorems/f6f158e3-2c77-423c-ba40-aaae32858ea9
-- title:
--   §5.1, p. 10 — the general solution $J(n)=l_1+l_2+k_1\alpha_-^n+k_2\alpha_+^n$ of (15)
-- statement:
--   Let $\lambda_1,\lambda_2,r>0$, let $l_1,l_2\ge1$ be natural numbers, and let $\alpha_\pm$ be the roots (4). A function $J:\mathbb Z\to\mathbb R$ satisfies the difference equation (15),
--
--   $$J(n)=(l_1+l_2)\frac{r}{r+\lambda_2+\lambda_1}+J(n+1)\frac{\lambda_2}{r+\lambda_2+\lambda_1}+J(n-1)\frac{\lambda_1}{r+\lambda_2+\lambda_1},$$
--
--   at every interior balance $-l_1<n<l_2$ if and only if there are real constants $k_1,k_2$ with
--
--   $$J(n)=l_1+l_2+k_1\alpha_-^{\,n}+k_2\alpha_+^{\,n}\qquad\text{for all } -l_1\le n\le l_2 .$$
--
--   This reduces the cost of a bidirectional channel to the two constants $k_1,k_2$, which the boundary conditions then determine.
--
--   **Formalization Note** Powers $\alpha_\pm^{\,n}$ with $n\in\mathbb Z$ are integer powers (`zpow`); the roots are positive under the hypotheses. Both directions are asserted.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 10 (PDF p. 11), §5.1, "The general solution to (15) is"

import Mathlib
import Definitions.Def_LNChannels_Exact_alphaPlus
import Definitions.Def_LNChannels_Exact_alphaMinus

set_option autoImplicit false

namespace LNChannels.Exact

/-- §5.1, p. 10: on the lattice `−l₁ ≤ n ≤ l₂`, `J` satisfies the difference equation (15) at
every interior balance `−l₁ < n < l₂` if and only if `J(n) = l₁ + l₂ + k₁ α₋ⁿ + k₂ α₊ⁿ` there for
some constants `k₁, k₂` (integer powers, `zpow`). -/
theorem general_solution (lam₁ lam₂ r : ℝ) (l₁ l₂ : ℕ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hr : 0 < r) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (J : ℤ → ℝ) :
    let a := alphaMinus lam₁ lam₂ r
    let b := alphaPlus lam₁ lam₂ r
    (∀ n : ℤ, -(l₁ : ℤ) < n → n < (l₂ : ℤ) →
        J n = ((l₁ : ℝ) + l₂) * (r / (r + lam₂ + lam₁))
              + J (n + 1) * (lam₂ / (r + lam₂ + lam₁))
              + J (n - 1) * (lam₁ / (r + lam₂ + lam₁))) ↔
      ∃ k₁ k₂ : ℝ, ∀ n : ℤ, -(l₁ : ℤ) ≤ n → n ≤ (l₂ : ℤ) →
        J n = (l₁ : ℝ) + l₂ + k₁ * a ^ n + k₂ * b ^ n := by sorry

end LNChannels.Exact
