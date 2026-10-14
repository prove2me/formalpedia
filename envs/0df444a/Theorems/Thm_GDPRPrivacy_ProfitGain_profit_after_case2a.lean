-- Prove2me | Theorems.Thm_GDPRPrivacy_ProfitGain_profit_after_case2a
-- name    : GDPRPrivacy.ProfitGain.profit_after_case2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:31.376155+00:00
-- url     : https://prove2.me/theorems/04492ea4-48b7-440f-a354-d0ac7f04be07
-- title:
--   Appendix, p. 32 — equilibrium profit after the GDPR, Π̃⋆ = Π̃⋆_2a = (4 + 4x(x + 2α + 2αx) + x²(x − 2α)²)/16 when α < α₂(x)
-- statement:
--   Consider the model with opt-in benefit $x\in(0,1)$ and data revenue $\alpha\ge 0$. After the GDPR the firm's profit at price $p\in\mathbb R$ is $\widetilde\Pi(p)=p\,\widetilde D(p)+\alpha\,\widetilde D_S(p)$. Here $\widetilde D$ is the total demand and $\widetilde D_S$ the opt-in demand.
--
--   If $\alpha<\alpha_2(x)=\max\{(2-4x+x^2)/(2x),0\}$, then $\widetilde\Pi$ attains its maximum over $\mathbb R$, and the maximal profit is
--   $$
--   \widetilde\Pi^\star=\widetilde\Pi^\star_{2a}=\frac{4+4x(x+2\alpha+2\alpha x)+x^2(x-2\alpha)^2}{16}.
--   $$
--
--   This is the equilibrium profit after the GDPR in the regime where the equilibrium price exceeds the opt-in benefit. It is the other closed form that Proposition A3 compares.
--
--   **Formalization Note.** The conclusion asserts that a maximizer exists and that every global maximizer of $\widetilde\Pi$ on $\mathbb R$ attains the value above. The hypothesis is $\alpha<\alpha_2(x)$, as printed. Proposition A3 uses it under the stronger $\alpha<\alpha_1(x)$, since $\alpha_1(x)\le\alpha_2(x)$ on $(0,1)$. The standing assumptions $0<x<1$ and $\alpha\ge0$ are hypotheses.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), p. 32, display for Π̃⋆ (Appendix, 'Equilibrium after the GDPR')

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.ProfitGain

/-- Appendix, p. 32: when `α < α₂(x)`, the equilibrium profit after the GDPR is
`Π̃⋆ = Π̃⋆_2a = (4 + 4x(x + 2α + 2αx) + x²(x - 2α)²)/16`. A maximizer of `Π̃` over `ℝ` exists, and
every maximizer attains this value. -/
theorem profit_after_case2a (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α)
    (hα2 : α < GDPRPrivacy.PriceRise.alpha2 x) :
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ p) ∧
    ∀ p, IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ p →
      GDPRPrivacy.PriceRise.profitAfter x α p =
        (4 + 4 * x * (x + 2 * α + 2 * α * x) + x ^ 2 * (x - 2 * α) ^ 2) / 16 := by sorry

end GDPRPrivacy.ProfitGain
