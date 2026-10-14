-- Prove2me | Theorems.Thm_GDPRPrivacy_ProfitGain_propA3_profit_higher_small_alpha
-- name    : GDPRPrivacy.ProfitGain.propA3_profit_higher_small_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:34.646435+00:00
-- url     : https://prove2.me/theorems/e595dc48-2182-4113-b3ad-af727fb665fb
-- title:
--   Proposition A3, first bullet, p. 34 — when α < α₁(x), the firm's equilibrium profit is larger after the GDPR, Π̃⋆_2a > Π̂⋆_1a
-- statement:
--   Consider a monopolist selling an online service at zero marginal cost to consumers with types $(v,c)$ uniform on $[0,1]^2$. The firm gives an opt-in benefit $x\in(0,1)$ to consumers who share data, and earns $\alpha\ge 0$ per unit of collected data. Before the GDPR every buyer shares data, and the profit at price $p$ is $\widehat\Pi(p)=(p+\alpha)\widehat D(p)$. After the GDPR consumers may buy without sharing, and the profit is $\widetilde\Pi(p)=p\,\widetilde D(p)+\alpha\,\widetilde D_S(p)$. An equilibrium price is a global maximizer of the profit over $p\in\mathbb R$.
--
--   If
--   $$
--   \alpha<\alpha_1(x)=\max\Big\{\frac{1-2x}{2},0\Big\},
--   $$
--   then both regimes have an equilibrium price, and the firm's equilibrium profit is strictly larger after the GDPR:
--   $$
--   \widetilde\Pi^\star_{2a}=\max_{p\in\mathbb R}\widetilde\Pi(p)\;>\;\max_{p\in\mathbb R}\widehat\Pi(p)=\widehat\Pi^\star_{1a}.
--   $$
--
--   The result says that a firm whose revenue is mostly usage based, with a small data revenue $\alpha$, gains from the GDPR. Opt-out purchase draws in consumers with high privacy costs, and the firm's lost data revenue is outweighed by its larger sales revenue.
--
--   **Formalization Note.** The conclusion asserts that maximizers of $\widehat\Pi$ and $\widetilde\Pi$ over all of $\mathbb R$ exist, and that $\widehat\Pi(\widehat p)<\widetilde\Pi(\widetilde p)$ for every maximizer $\widehat p$ of $\widehat\Pi$ and every maximizer $\widetilde p$ of $\widetilde\Pi$. Each profit is evaluated at its own regime's optimal price, not at a common price. The subscripts 1a and 2a are not hypotheses: Lemma A3 shows that $\alpha<\alpha_1(x)$ places both equilibria in those cases. Since $\alpha\ge0$, the hypothesis forces $x<1/2$. The standing assumptions $0<x<1$ and $\alpha\ge0$ are hypotheses.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), p. 34, Proposition A3 (first bullet); proof OA p. 9, §F

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.ProfitGain

/-- Proposition A3, first bullet (p. 34): when `α < α₁(x)`, the firm's equilibrium profit is
larger after the GDPR, `Π̃⋆_2a > Π̂⋆_1a`. Equilibrium prices are global maximizers of the profit
over all of `ℝ`; both exist, and the maximal profit after the GDPR exceeds the maximal profit before
it. -/
theorem propA3_profit_higher_small_alpha (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α)
    (hα1 : α < GDPRPrivacy.PriceRise.alpha1 x) :
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ p) ∧
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ p) ∧
    ∀ pHat pTilde, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ pHat →
      IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ pTilde →
      GDPRPrivacy.PriceRise.profitBefore x α pHat < GDPRPrivacy.PriceRise.profitAfter x α pTilde := by sorry

end GDPRPrivacy.ProfitGain
