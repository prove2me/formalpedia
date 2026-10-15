-- Prove2me | Theorems.Thm_LNChannels_Walk_equation_30
-- name    : LNChannels.Walk.equation_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:57.864393+00:00
-- url     : https://prove2.me/theorems/06b5701f-7f08-46ba-947d-6336b3a47dca
-- title:
--   (30), proof of Proposition 2, p. 13 — m(0) = (q^{l₁} − 1)(q^{l₂} − 1)/((l₂(q^{l₁} − 1) − l₁)q^{l₂} + l₁)
-- statement:
--   Let $\lambda_1,\lambda_2>0$ with $\lambda_1\neq\lambda_2$, let $q=\lambda_2/\lambda_1$, and let $l_1,l_2\ge1$ be the channel sizes. Let $m$ be any stationary distribution of the reset walk. Then its mass at the balance $0$ is
--   $$
--   m(0)=\frac{(q^{l_1}-1)(q^{l_2}-1)}{\bigl(l_2(q^{l_1}-1)-l_1\bigr)q^{l_2}+l_1}.
--   $$
--
--   The masses (28) and (29) are multiples of $m(0)$. The normalization $\sum_{n=-l_1}^{l_2}m(n)=1$ is a linear equation in $m(0)$, and (30) is its solution. Together, (28)–(30) determine the stationary distribution completely.
--
--   **Formalization Note** The hypothesis $q\neq1$ is added as in (28) and (29).
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 13 (PDF 14), proof of Proposition 2, (30)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LNChannels_Walk_ResetWalk

namespace LNChannels.Walk

/-- (30), proof of Proposition 2, p. 13: for every stationary distribution `m` of the reset walk,
`m(0) = (q^{l₁} − 1)(q^{l₂} − 1)/((l₂(q^{l₁} − 1) − l₁) q^{l₂} + l₁)` with `q = λ₂/λ₁`. -/
theorem equation_30 (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hne : lam₁ ≠ lam₂) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (q : ℝ) (hq : q = lam₂ / lam₁)
    (m : Fin (l₁ + l₂ - 1) → ℝ) (hm : MarkovMixing.IsStationary (resetWalk lam₁ lam₂ l₁ l₂) m) :
    massAt l₁ l₂ m 0 =
      (q ^ l₁ - 1) * (q ^ l₂ - 1) / (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁) := by sorry

end LNChannels.Walk
