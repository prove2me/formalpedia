-- Prove2me | Theorems.Thm_LNChannels_Walk_proposition_2
-- name    : LNChannels.Walk.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:57.554987+00:00
-- url     : https://prove2.me/theorems/713dc3a1-039f-4f74-9f82-9bc92a5628e3
-- title:
--   Proposition 2 (Congestion Reduction), p. 9 — channel transactions per on-chain transaction = (q + 1)((l₂(q^{l₁} − 1) − l₁)q^{l₂} + l₁)/((q − 1)(q^{l₁+l₂} − 1))
-- statement:
--   Consider a bidirectional payment channel with sizes $l_1,l_2\ge1$ and payment rates $\lambda_1,\lambda_2>0$ with $\lambda_1\neq\lambda_2$, and let $q=\lambda_2/\lambda_1$. Each channel transaction moves the balance up by one with probability $\lambda_2/(\lambda_1+\lambda_2)$ and down by one with probability $\lambda_1/(\lambda_1+\lambda_2)$. When the balance reaches $l_2$ or $-l_1$, an on-chain transaction resets it to $0$. Then:
--
--   1. the reset walk has a stationary distribution $m$;
--   2. for every stationary distribution $m$, the long-term ratio between the number of channel transactions and the number of on-chain transactions equals
--   $$
--   \frac{(q+1)\Bigl(\bigl(l_2(q^{l_1}-1)-l_1\bigr)q^{l_2}+l_1\Bigr)}{(q-1)(q^{l_1+l_2}-1)}.
--   $$
--   This ratio is the reciprocal of the fraction $m(l_2-1)\frac{\lambda_2}{\lambda_1+\lambda_2}+m(-l_1+1)\frac{\lambda_1}{\lambda_1+\lambda_2}$ of transactions that trigger a reset.
--
--   Channels reduce congestion on the blockchain: each on-chain transaction now carries this many channel transactions. As $q\downarrow0$ the number tends to $l_1$, and as $q\to1$ it tends to $l_1l_2$.
--
--   **Formalization Note** The "long-term ratio" is read, as in the paper's proof, as the reciprocal of the stationary fraction of reset-triggering transactions. Identifying it with a pathwise long-run average is an ergodic theorem that the paper does not state. The hypothesis $\lambda_1\neq\lambda_2$ is added, because the formula divides by $q-1$; the paper treats $q=1$ only as the limit (ii). The existence clause keeps the statement from being vacuous. Uniqueness of $m$ is not assumed: the statement holds for every stationary $m$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 9 (PDF 10), Proposition 2; proof p. 13 (PDF 14)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LNChannels_Walk_ResetWalk

namespace LNChannels.Walk

/-- **Proposition 2** (Congestion Reduction), p. 9: in a bidirectional channel with sizes
`l₁, l₂ ≥ 1` and rates `λ₁, λ₂ > 0`, `λ₁ ≠ λ₂`, the reset walk has a stationary distribution,
and for every stationary distribution `m` the long-term ratio between channel and on-chain
transactions, the reciprocal of the fraction of transactions that trigger a reset, equals
`(q + 1)((l₂(q^{l₁} − 1) − l₁) q^{l₂} + l₁)/((q − 1)(q^{l₁+l₂} − 1))` with `q = λ₂/λ₁`. -/
theorem proposition_2 (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hne : lam₁ ≠ lam₂) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (q : ℝ) (hq : q = lam₂ / lam₁) :
    (∃ m : Fin (l₁ + l₂ - 1) → ℝ, MarkovMixing.IsStationary (resetWalk lam₁ lam₂ l₁ l₂) m) ∧
    ∀ m : Fin (l₁ + l₂ - 1) → ℝ, MarkovMixing.IsStationary (resetWalk lam₁ lam₂ l₁ l₂) m →
      1 / resetFraction lam₁ lam₂ l₁ l₂ m =
        (q + 1) * (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁) /
          ((q - 1) * (q ^ (l₁ + l₂) - 1)) := by sorry

end LNChannels.Walk
