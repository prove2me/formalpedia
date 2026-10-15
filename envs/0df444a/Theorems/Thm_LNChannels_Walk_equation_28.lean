-- Prove2me | Theorems.Thm_LNChannels_Walk_equation_28
-- name    : LNChannels.Walk.equation_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:47.450202+00:00
-- url     : https://prove2.me/theorems/8f39c55b-aede-47c9-98c5-f01c007cac3d
-- title:
--   (28), proof of Proposition 2, p. 13 — m(n) = m(0)(q^{l₂} − qⁿ)/(q^{l₂} − 1) for 0 ≤ n ≤ l₂
-- statement:
--   Let $\lambda_1,\lambda_2>0$ with $\lambda_1\neq\lambda_2$, let $q=\lambda_2/\lambda_1$, and let $l_1,l_2\ge1$ be the channel sizes. Let $m$ be any stationary distribution of the reset walk, the channel balance that is reset to $0$ whenever it reaches $l_2$ or $-l_1$, and let $m(n)$ be its mass at the balance $n$, with $m(l_2)=0$. Then for every $0\le n\le l_2$,
--   $$
--   m(n)=m(0)\,\frac{q^{l_2}-q^{n}}{q^{l_2}-1}.
--   $$
--
--   This solves the balance equation (27), $m(n)=\frac{\lambda_2}{\lambda_1+\lambda_2}m(n-1)+\frac{\lambda_1}{\lambda_1+\lambda_2}m(n+1)$ for $0<n<l_2$, with the boundary value $m(l_2)=0$. It gives the stationary masses at the nonnegative balances in terms of $m(0)$.
--
--   **Formalization Note** At $n=l_2$ both sides vanish: the left side is $0$ by the convention that the reset walk never occupies $l_2$. The hypothesis $\lambda_1\neq\lambda_2$ ($q\neq1$) keeps the denominator nonzero. The paper does not print it with (28), but the formula needs it.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 13 (PDF 14), proof of Proposition 2, (28)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LNChannels_Walk_ResetWalk

namespace LNChannels.Walk

/-- (28), proof of Proposition 2, p. 13: for every stationary distribution `m` of the reset walk
and `0 ≤ n ≤ l₂`, `m(n) = m(0) (q^{l₂} − q^n)/(q^{l₂} − 1)` with `q = λ₂/λ₁`
(at `n = l₂` both sides vanish: `m(l₂) = 0` is the paper's convention). -/
theorem equation_28 (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hne : lam₁ ≠ lam₂) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (q : ℝ) (hq : q = lam₂ / lam₁)
    (m : Fin (l₁ + l₂ - 1) → ℝ) (hm : MarkovMixing.IsStationary (resetWalk lam₁ lam₂ l₁ l₂) m) :
    ∀ n : ℕ, n ≤ l₂ →
      massAt l₁ l₂ m (n : ℤ) = massAt l₁ l₂ m 0 * (q ^ l₂ - q ^ n) / (q ^ l₂ - 1) := by sorry

end LNChannels.Walk
