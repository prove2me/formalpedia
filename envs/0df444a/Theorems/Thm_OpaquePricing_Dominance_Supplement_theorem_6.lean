-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_theorem_6
-- name    : OpaquePricing.Dominance.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:43:19.1925+00:00
-- url     : https://prove2.me/theorems/8d68b606-a4de-4d5a-999f-bc665c60126c
-- title:
--   Theorem 6 — Equal allocation maximizes optimized two-item opaque revenue
-- statement:
--   Consider two items, risk-neutral customers, and an exchangeable nonnegative valuation law $\mu$ supported almost surely on two common values $a<b$. For every announced allocation probability $\beta\in(1/2,1]$,
--   $$R_{OPQ}(\mu;\cdot,1/2)\ge R_{OPQ}(\mu;\cdot,\beta).$$
--   At each $\beta$, the two item options have one common price and the full-set lottery has another price, optimized independently. The lottery values are $\beta v_1+(1-\beta)v_2$. The result asserts optimality of equal allocation, with no assertion of uniqueness.
--
--   Differences from the source:
--   - encoding: the N=2 risk-neutral model inherited from Appendix A → a law on Fin 2 → ℝ and the fixed-risk-neutral announced allocation menu; reason: makes the section’s dimension and customer type explicit, including a zero low value and atomic laws
--   - encoding: nonnegative prices, expected revenues, and optimal prices → published highest-price choice revenue, nonnegative real prices, and ENNReal expectations and suprema; reason: preserves atomic and unbounded laws without an integrability or attained-optimum premise; the inherited supremum convention is disclosed in the published base mission
--   - reading: the centered dot in R_OPQ(·,β) → a separate supremum over the two nonnegative prices for each β; reason: the p. 34 discussion and proof optimize prices at each probability; the same fixed prices need not work at both probabilities
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Theorem 6, p. 34

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_Allocation

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

theorem theorem_6 (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hex : Exchangeable μ) (htwo : TwoValued μ)
    (β : ℝ) (hβ : β ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    optAllocation μ β ≤ optAllocation μ (1 / 2) := by sorry

end OpaquePricing.Dominance.Supplement
