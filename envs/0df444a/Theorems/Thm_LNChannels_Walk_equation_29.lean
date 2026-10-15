-- Prove2me | Theorems.Thm_LNChannels_Walk_equation_29
-- name    : LNChannels.Walk.equation_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:43.290216+00:00
-- url     : https://prove2.me/theorems/084d586f-59a1-47ee-b346-7c7424564748
-- title:
--   (29), proof of Proposition 2, p. 13 — m(n) = m(0)(q^{l₁+n} − 1)/(q^{l₁} − 1) for −l₁ ≤ n ≤ 0
-- statement:
--   Let $\lambda_1,\lambda_2>0$ with $\lambda_1\neq\lambda_2$, let $q=\lambda_2/\lambda_1$, and let $l_1,l_2\ge1$ be the channel sizes. Let $m$ be any stationary distribution of the reset walk, and let $m(n)$ be its mass at the balance $n$, with $m(-l_1)=0$. Then for every $-l_1\le n\le0$,
--   $$
--   m(n)=m(0)\,\frac{q^{l_1+n}-1}{q^{l_1}-1}.
--   $$
--
--   This is the counterpart of (28) for the nonpositive balances. It solves the same balance equation (27) on $-l_1<n<0$ with the boundary value $m(-l_1)=0$.
--
--   **Formalization Note** The exponent $l_1+n$ is an integer, and the power is an integer power of $q>0$. At $n=-l_1$ both sides vanish by the convention $m(-l_1)=0$. The hypothesis $q\neq1$ keeps the denominator nonzero; the paper does not print it.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 13 (PDF 14), proof of Proposition 2, (29)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LNChannels_Walk_ResetWalk

namespace LNChannels.Walk

/-- (29), proof of Proposition 2, p. 13: for every stationary distribution `m` of the reset walk
and `−l₁ ≤ n ≤ 0`, `m(n) = m(0) (q^{l₁+n} − 1)/(q^{l₁} − 1)` with `q = λ₂/λ₁`
(at `n = −l₁` both sides vanish: `m(−l₁) = 0` is the paper's convention). -/
theorem equation_29 (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hne : lam₁ ≠ lam₂) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (q : ℝ) (hq : q = lam₂ / lam₁)
    (m : Fin (l₁ + l₂ - 1) → ℝ) (hm : MarkovMixing.IsStationary (resetWalk lam₁ lam₂ l₁ l₂) m) :
    ∀ n : ℤ, -(l₁ : ℤ) ≤ n → n ≤ 0 →
      massAt l₁ l₂ m n = massAt l₁ l₂ m 0 * (q ^ ((l₁ : ℤ) + n) - 1) / (q ^ l₁ - 1) := by sorry

end LNChannels.Walk
