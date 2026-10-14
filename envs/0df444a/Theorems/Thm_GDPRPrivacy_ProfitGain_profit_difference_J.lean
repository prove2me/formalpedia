-- Prove2me | Theorems.Thm_GDPRPrivacy_ProfitGain_profit_difference_J
-- name    : GDPRPrivacy.ProfitGain.profit_difference_J
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:28.778202+00:00
-- url     : https://prove2.me/theorems/cdc0021d-aa26-4f0c-86f7-773227c47e61
-- title:
--   Online Appendix §F, OA p. 9, first display — Π̃⋆ − Π̂⋆ = J(x, α)/432 when α < α₁(x)
-- statement:
--   Consider the model with opt-in benefit $x\in(0,1)$ and data revenue $\alpha\ge 0$. Let $\widehat\Pi^\star$ and $\widetilde\Pi^\star$ be the equilibrium profits before and after the GDPR, i.e. the maximal values of $\widehat\Pi$ and $\widetilde\Pi$ over $p\in\mathbb R$.
--
--   If $\alpha<\alpha_1(x)$, both maxima are attained and
--   $$
--   \widetilde\Pi^\star-\widehat\Pi^\star=\frac{76+27x^4-96\alpha-32\alpha^2(3+\alpha)+12x^2(1+\alpha)(1+9\alpha)}{432}-\frac{4x^3(8+27\alpha)+24x(4+4\alpha^2-\alpha)}{432}.
--   $$
--
--   The numerator of this difference is the polynomial $J(x,\alpha)$. Proposition A3 then reduces to showing $J>0$.
--
--   **Formalization Note.** The conclusion asserts that both maximizers exist and that the identity holds for every pair of maximizers $(\widehat p^\star,\widetilde p^\star)$, with $\widetilde\Pi^\star-\widehat\Pi^\star$ read as $\widetilde\Pi(\widetilde p^\star)-\widehat\Pi(\widehat p^\star)$. The minus sign in front of the second fraction applies to the whole fraction, as on the rendered page. The standing assumptions $0<x<1$ and $\alpha\ge0$ are hypotheses.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), OA p. 9, §F (Proof of Proposition A3), first display

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.ProfitGain

/-- Online Appendix §F, first display (OA p. 9): when `α < α₁(x)`, the difference of the
equilibrium profits is
`Π̃⋆ - Π̂⋆ = (76 + 27x⁴ - 96α - 32α²(3 + α) + 12x²(1 + α)(1 + 9α))/432
             - (4x³(8 + 27α) + 24x(4 + 4α² - α))/432`.
Both maximizers exist, and the identity holds for every pair of maximizers. -/
theorem profit_difference_J (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α)
    (hα1 : α < GDPRPrivacy.PriceRise.alpha1 x) :
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ p) ∧
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ p) ∧
    ∀ pHat pTilde, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ pHat →
      IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ pTilde →
      GDPRPrivacy.PriceRise.profitAfter x α pTilde - GDPRPrivacy.PriceRise.profitBefore x α pHat =
        (76 + 27 * x ^ 4 - 96 * α - 32 * α ^ 2 * (3 + α)
            + 12 * x ^ 2 * (1 + α) * (1 + 9 * α)) / 432
          - (4 * x ^ 3 * (8 + 27 * α) + 24 * x * (4 + 4 * α ^ 2 - α)) / 432 := by sorry

end GDPRPrivacy.ProfitGain
