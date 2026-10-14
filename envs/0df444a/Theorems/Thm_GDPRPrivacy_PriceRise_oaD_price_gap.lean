-- Prove2me | Theorems.Thm_GDPRPrivacy_PriceRise_oaD_price_gap
-- name    : GDPRPrivacy.PriceRise.oaD_price_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:30.804983+00:00
-- url     : https://prove2.me/theorems/cd717109-ec8c-4906-896c-ab417d413ef4
-- title:
--   OA §D, OA p. 7, first display — the price gap p̃⋆ − p̂⋆ in the three regions
-- statement:
--   Let $0 < x < 1$ and $\alpha \ge 0$, and let $\beta = \sqrt{6 + (x+\alpha-1)^2}$ and $\Gamma = \sqrt{6 + (2-2x+\alpha)^2}$. The pre- and post-GDPR profits $\widehat\Pi$, $\widetilde\Pi$ have global maximizers over $\mathbb{R}$, and for any maximizers $\hat p^\star$ of $\widehat\Pi$ and $\tilde p^\star$ of $\widetilde\Pi$,
--   $$\tilde p^\star - \hat p^\star = \begin{cases} \dfrac{2 + 8\alpha - x(4 + 6\alpha - 3x)}{12} & \text{if } \alpha < \alpha_1(x),\\[2mm] \dfrac{14 + 4\alpha + 3x^2 - 8x - 6x\alpha - 4\beta}{12} & \text{if } \alpha_1(x) \le \alpha < \alpha_2(x),\\[2mm] \dfrac{\Gamma - \beta}{3} & \text{if } \alpha_2(x) \le \alpha. \end{cases}$$
--
--   This reduces the comparison of equilibrium prices to the sign of three explicit expressions in $(x, \alpha)$, one per region of Lemma A3.
--
--   **Formalization Note** The existence conjuncts make the identity, which is stated for every pair of maximizers, non-vacuous.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), OA p. 7, §D (Proof of Proposition A1), first display

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.PriceRise

theorem oaD_price_gap (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) :
    (∃ p, IsMaxOn (profitBefore x α) Set.univ p) ∧
    (∃ p, IsMaxOn (profitAfter x α) Set.univ p) ∧
    ∀ pHat pTilde : ℝ,
      IsMaxOn (profitBefore x α) Set.univ pHat →
      IsMaxOn (profitAfter x α) Set.univ pTilde →
        (α < alpha1 x →
          pTilde - pHat = (2 + 8 * α - x * (4 + 6 * α - 3 * x)) / 12) ∧
        (alpha1 x ≤ α → α < alpha2 x →
          pTilde - pHat = (14 + 4 * α + 3 * x ^ 2 - 8 * x - 6 * x * α - 4 * beta x α) / 12) ∧
        (alpha2 x ≤ α →
          pTilde - pHat = (Gamma x α - beta x α) / 3) := by sorry

end GDPRPrivacy.PriceRise
