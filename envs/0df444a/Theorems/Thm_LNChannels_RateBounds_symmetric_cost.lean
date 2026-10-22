-- Prove2me | Theorems.Thm_LNChannels_RateBounds_symmetric_cost
-- name    : LNChannels.RateBounds.symmetric_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:45.073194+00:00
-- url     : https://prove2.me/theorems/8107455d-d7b1-4c07-b630-04b076e05465
-- title:
--   Proof of Theorem 2(ii), p. 11 — the cost of a symmetric channel is $l_1+l_2+B(\alpha^{l_1}+\alpha^{l_2})/((\alpha^{l_1}-1)(\alpha^{l_2}-1))$
-- statement:
--   Let $\lambda,r>0$, $B\in\mathbb R$ and real sizes $l_1,l_2>0$. Put $\lambda_1=\lambda_2=\lambda$ in (4) and let $\alpha=\alpha_+$. Then
--   1. $\alpha=\dfrac{r+2\lambda+\sqrt{r(4\lambda+r)}}{2\lambda}$ and $\alpha>1$;
--   2. the bidirectional cost (3) of the symmetric channel is
--   $$c^{l_1,l_2}(\lambda,\lambda)=l_1+l_2+\frac{B(\alpha^{l_1}+\alpha^{l_2})}{(\alpha^{l_1}-1)(\alpha^{l_2}-1)};$$
--   3. $\dfrac{\lambda}{r}=\dfrac{\alpha}{(\alpha-1)^2}$, so that the on-chain cost $2C\lambda/r$ of the two streams equals $2C\alpha/(\alpha-1)^2$.
--
--   These identities reduce Theorem 2(ii) to the sign of a function of $l_1,l_2$ and $\alpha$ alone.
--
--   **Formalization Note** The cost is the closed form `biCost` of (3) at $\lambda_1=\lambda_2=\lambda$ with real sizes and real powers.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 11 (PDF p. 12), proof of Theorem 2(ii), first two displays

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- Proof of Theorem 2(ii), p. 11: for `λ₁ = λ₂ = λ` the cost (3) is
`l₁ + l₂ + B(α^{l₁} + α^{l₂})/((α^{l₁} − 1)(α^{l₂} − 1))` with
`α = α₊ = (r + 2λ + √(r(4λ + r)))/(2λ) > 1`, and `λ/r = α/(α − 1)²`. -/
theorem symmetric_cost (lam r B l₁ l₂ : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) :
    let α := LNChannels.Exact.alphaPlus lam lam r
    α = (r + 2 * lam + √(r * (4 * lam + r))) / (2 * lam) ∧
      1 < α ∧
      biCost lam lam r B l₁ l₂ =
        l₁ + l₂ + B * (α ^ l₁ + α ^ l₂) / ((α ^ l₁ - 1) * (α ^ l₂ - 1)) ∧
      lam / r = α / (α - 1) ^ 2 := by sorry

end LNChannels.RateBounds
