-- Prove2me | Theorems.Thm_GDPRPrivacy_ProfitGain_profit_before_case1a
-- name    : GDPRPrivacy.ProfitGain.profit_before_case1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:24.934466+00:00
-- url     : https://prove2.me/theorems/beab36b9-7c19-44f7-8f23-debe05616b15
-- title:
--   Appendix, p. 31 — equilibrium profit before the GDPR, Π̂⋆ = Π̂⋆_1a = 2(1 + x + α)³/27 when α < α₁(x)
-- statement:
--   Consider the model with opt-in benefit $x\in(0,1)$ and data revenue $\alpha\ge 0$. Before the GDPR, every buyer shares data and the firm's profit at price $p\in\mathbb R$ is $\widehat\Pi(p)=(p+\alpha)\widehat D(p)$.
--
--   If $\alpha<\alpha_1(x)=\max\{(1-2x)/2,0\}$, then $\widehat\Pi$ attains its maximum over $\mathbb R$, and the maximal profit is
--   $$
--   \widehat\Pi^\star=\widehat\Pi^\star_{1a}=\frac{2(1+x+\alpha)^3}{27}.
--   $$
--
--   This is the equilibrium profit of a firm whose revenue before the GDPR is mostly usage based. It is one of the two closed forms that Proposition A3 compares.
--
--   **Formalization Note.** The conclusion asserts that a maximizer exists and that every global maximizer of $\widehat\Pi$ on $\mathbb R$ attains the value above. The standing assumptions $0<x<1$ and $\alpha\ge0$ are hypotheses.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), p. 31, display for Π̂⋆ (Appendix, 'Equilibrium before the GDPR')

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.ProfitGain

/-- Appendix, p. 31: when `α < α₁(x)`, the equilibrium profit before the GDPR is
`Π̂⋆ = Π̂⋆_1a = 2(1 + x + α)³/27`. A maximizer of `Π̂` over `ℝ` exists, and every maximizer attains
this value. -/
theorem profit_before_case1a (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α)
    (hα1 : α < GDPRPrivacy.PriceRise.alpha1 x) :
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ p) ∧
    ∀ p, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ p →
      GDPRPrivacy.PriceRise.profitBefore x α p = 2 * (1 + x + α) ^ 3 / 27 := by sorry

end GDPRPrivacy.ProfitGain
