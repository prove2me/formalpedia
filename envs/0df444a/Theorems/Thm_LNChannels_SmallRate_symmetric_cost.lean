-- Prove2me | Theorems.Thm_LNChannels_SmallRate_symmetric_cost
-- name    : LNChannels.SmallRate.symmetric_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:53.948367+00:00
-- url     : https://prove2.me/theorems/9ce083d0-6c75-483e-a2d4-77002c0eef27
-- title:
--   Symmetric bidirectional cost formula
-- statement:
--   Let $\lambda,r>0$, let $B$ be a real reset cost, and let $l_1,l_2>0$. With $\alpha=\alpha_+(\lambda,\lambda,r)>1$, the equal-rate specialization of equation (3) is
--
--   $$c^{l_1,l_2}(\lambda,\lambda)=l_1+l_2+\frac{B(\alpha^{l_1}+\alpha^{l_2})}{(\alpha^{l_1}-1)(\alpha^{l_2}-1)}.$$
--
--   This form makes the symmetric optimization problem explicit. **Formalization Note** The sizes here are positive real numbers, as in the paper's differentiable minimization.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 11 (PDF 12), proof of Theorem 2(ii), symmetric-cost display

import Definitions.Def_LNChannels_RateBounds_ClosedForms

set_option autoImplicit false

namespace LNChannels.SmallRate

/-- The symmetric-cost display in the proof of Theorem 2(ii), p. 11. -/
theorem symmetric_cost (lam r B l₁ l₂ : ℝ) (hlam : 0 < lam) (hr : 0 < r)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) :
    let a := LNChannels.Exact.alphaPlus lam lam r
    1 < a ∧ LNChannels.RateBounds.biCost lam lam r B l₁ l₂ =
      l₁ + l₂ + B * (a ^ l₁ + a ^ l₂) / ((a ^ l₁ - 1) * (a ^ l₂ - 1)) := by sorry

end LNChannels.SmallRate
