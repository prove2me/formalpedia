-- Prove2me | Theorems.Thm_LNChannels_Walk_on_chain_fraction
-- name    : LNChannels.Walk.on_chain_fraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:54.635164+00:00
-- url     : https://prove2.me/theorems/93e37b0a-0a93-4133-88a2-5315d078c1d3
-- title:
--   Proof of Proposition 2, p. 13 — the fraction of channel transactions that trigger an on-chain transaction
-- statement:
--   Let $\lambda_1,\lambda_2>0$ with $\lambda_1\neq\lambda_2$, let $q=\lambda_2/\lambda_1$, and let $l_1,l_2\ge1$ be the channel sizes. Let $m$ be any stationary distribution of the reset walk. The channel transactions that lead to an on-chain transaction are the up-moves from $l_2-1$ and the down-moves from $-l_1+1$, and their fraction is
--   $$
--   m(l_2-1)\,\frac{\lambda_2}{\lambda_1+\lambda_2}+m(-l_1+1)\,\frac{\lambda_1}{\lambda_1+\lambda_2}
--   =\frac{(q-1)\,(q^{l_1+l_2}-1)}{(q+1)\Bigl(\bigl(l_2(q^{l_1}-1)-l_1\bigr)q^{l_2}+l_1\Bigr)}.
--   $$
--
--   The paper evaluates the left side by (28), (29) and (30). Its reciprocal is the long-run number of channel transactions per on-chain transaction of Proposition 2.
--
--   **Formalization Note** The paper states this display without its value ("its value is obtained from (28), (29), and (30)"). The right side is that value, the reciprocal of the formula of Proposition 2. The hypothesis $q\neq1$ is added. When $l_1=1$ the bottom balance $-l_1+1$ is the balance $0$ itself; when $l_2=1$ the top balance $l_2-1$ is the balance $0$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 13 (PDF 14), proof of Proposition 2, display after (30)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LNChannels_Walk_ResetWalk

namespace LNChannels.Walk

/-- Proof of Proposition 2, p. 13: for every stationary distribution `m` of the reset walk, the
fraction of channel transactions that trigger an on-chain transaction,
`m(l₂ − 1) λ₂/(λ₁ + λ₂) + m(−l₁ + 1) λ₁/(λ₁ + λ₂)`, equals
`(q − 1)(q^{l₁+l₂} − 1)/((q + 1)((l₂(q^{l₁} − 1) − l₁) q^{l₂} + l₁))` with `q = λ₂/λ₁`. -/
theorem on_chain_fraction (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hne : lam₁ ≠ lam₂) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (q : ℝ) (hq : q = lam₂ / lam₁)
    (m : Fin (l₁ + l₂ - 1) → ℝ) (hm : MarkovMixing.IsStationary (resetWalk lam₁ lam₂ l₁ l₂) m) :
    resetFraction lam₁ lam₂ l₁ l₂ m =
      (q - 1) * (q ^ (l₁ + l₂) - 1) /
        ((q + 1) * (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁)) := by sorry

end LNChannels.Walk
