-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_theorem_1
-- name    : OpaquePricing.Dominance.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:06.628553+00:00
-- url     : https://prove2.me/theorems/9b31d868-8f8d-412a-a0e7-30b17eead338
-- title:
--   Theorem 1: opaque selling dominates discriminatory pricing
-- statement:
--   Let $N\ge2$. Customers have an exchangeable probability law on nonnegative item valuations, and a share $\alpha\in[0,1]$ are pessimistic about opaque products. If either every customer is pessimistic ($\alpha=1$) or the item valuations almost surely take only two common values, then
--
--   $$R_{\mathrm{OPQ}}^\alpha\ge R_{\mathrm{DP}}.$$
--
--   This is the paper's principal dominance theorem for size-priced opaque products.
--
--   **Formalization Note** Revenue follows the highest-price tie-break even for discrete valuation laws. Both optimal revenues are suprema in $[0,\infty]$ over nonnegative prices.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Theorem 1, p. 14

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance

theorem theorem_1 {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ0 : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hexch : Exchangeable μ)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcase : α = 1 ∨ TwoValued μ) :
    optDP μ ≤ optOPQ μ α := by sorry

end OpaquePricing.Dominance
