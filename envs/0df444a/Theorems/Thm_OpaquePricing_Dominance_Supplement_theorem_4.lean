-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_theorem_4
-- name    : OpaquePricing.Dominance.Supplement.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:39:48.838654+00:00
-- url     : https://prove2.me/theorems/dd9d840f-5e11-44a7-8071-b63923de6051
-- title:
--   Theorem 4 — One opaque product approximates discriminatory pricing
-- statement:
--   Let $N\ge2$, let $\mu$ be an exchangeable probability law whose nonnegative item valuations lie almost surely in a common pair $a<b$, and let $\alpha\in[0,1]$. Then
--   $$R_{1OPQ}(\mu,\alpha)\ge\frac{719}{1000}R_{DP}(\mu).$$
--   Only singleton items and the full-set opaque product may be sold. This guarantee retains the exact decimal constant 0.719 and includes $a=0$ and degenerate one-point laws supported within a pair.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - encoding: a pessimistic fraction α and a risk-neutral fraction 1−α → α ∈ [0,1] and the published independent mixture; reason: makes the probability range explicit and does not replace a mixture of revenues by a mixture of valuations
--   - encoding: nonnegative prices, expected revenues, and optimal prices → published highest-price choice revenue, nonnegative real prices, and ENNReal expectations and suprema; reason: preserves atomic and unbounded laws without an integrability or attained-optimum premise; the inherited supremum convention is disclosed in the published base mission
--   - encoding: 0.719 and common two-value support → the exact real rational 719/1000 and the published almost-sure TwoValued predicate; reason: no numerical weakening or normalization of the low value is used
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Theorem 4, p. 22

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_OneOpaque

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

theorem theorem_4 {N : ℕ} (hN : 2 ≤ N) (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (α : ℝ) (hα : α ∈ Set.Icc 0 1)
    (hex : Exchangeable μ) (htwo : TwoValued μ) :
    ENNReal.ofReal (719 / 1000 : ℝ) * optDP μ ≤ optOne μ α := by sorry

end OpaquePricing.Dominance.Supplement
