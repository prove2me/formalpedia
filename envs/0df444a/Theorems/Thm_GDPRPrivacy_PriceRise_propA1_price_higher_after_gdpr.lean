-- Prove2me | Theorems.Thm_GDPRPrivacy_PriceRise_propA1_price_higher_after_gdpr
-- name    : GDPRPrivacy.PriceRise.propA1_price_higher_after_gdpr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:19.858786+00:00
-- url     : https://prove2.me/theorems/bc9739ff-7952-4421-9681-9edb8f06d03c
-- title:
--   Proposition A1, p. 34 — the equilibrium price is higher after the GDPR, p̃⋆ > p̂⋆
-- statement:
--   Consider the monopoly model of the mission: consumer types $(v,c)$ uniform on $[0,1]^2$, opt-in benefit $x$, data revenue $\alpha$ per unit of shared data, pre-GDPR profit $\widehat\Pi(p) = (p+\alpha)\widehat D(p)$ and post-GDPR profit $\widetilde\Pi(p) = p\,\widetilde D(p) + \alpha\,\widetilde D_S(p)$, both functions of the price $p \in \mathbb{R}$.
--
--   For every $0 < x < 1$ and every $\alpha \ge 0$, both $\widehat\Pi$ and $\widetilde\Pi$ attain a global maximum on $\mathbb{R}$, and every maximizer $\hat p^\star$ of $\widehat\Pi$ and every maximizer $\tilde p^\star$ of $\widetilde\Pi$ satisfy
--   $$\tilde p^\star > \hat p^\star.$$
--
--   That is, the equilibrium price is strictly higher after the GDPR, whatever the opt-in benefit and whatever the mix of usage-based and data-based revenue. This is the paper's general, fully analytic price comparison; the main text's Proposition 1 is its instance $x = 1/4$.
--
--   **Formalization Note** The equilibrium price is modelled as a global maximizer of the profit over all real prices (the firm moves first, consumers respond). The existence conjuncts rule out a vacuous "every maximizer" statement; the paper's uniqueness of each maximizer is not part of the goal but follows from the milestones.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), p. 34, Proposition A1; proof OA p. 7, §D

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.PriceRise

theorem propA1_price_higher_after_gdpr (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) :
    (∃ p, IsMaxOn (profitBefore x α) Set.univ p) ∧
    (∃ p, IsMaxOn (profitAfter x α) Set.univ p) ∧
    ∀ pHat pTilde : ℝ,
      IsMaxOn (profitBefore x α) Set.univ pHat →
      IsMaxOn (profitAfter x α) Set.univ pTilde →
        pHat < pTilde := by sorry

end GDPRPrivacy.PriceRise
