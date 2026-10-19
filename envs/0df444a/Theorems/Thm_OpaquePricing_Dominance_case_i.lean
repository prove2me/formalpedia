-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_case_i
-- name    : OpaquePricing.Dominance.case_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:00.482001+00:00
-- url     : https://prove2.me/theorems/f160b694-92ef-49a8-b55a-5c507898e2e1
-- title:
--   Theorem 1, Case (i): pessimistic opaque selling dominates DP
-- statement:
--   Let $N\ge2$ and let $F$ be an exchangeable probability law on nonnegative item valuations. When every customer is pessimistic about opaque products,
--
--   $$R_{\mathrm{DP}}\le R_{\mathrm{OPQ}}^1.$$
--
--   This is the first branch of Theorem 1 and applies to laws with valuation ties.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), proof of Theorem 1, Case (i), pp. 18–19

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance

theorem case_i {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ0 : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hexch : Exchangeable μ) :
    optDP μ ≤ optOPQ μ 1 := by sorry

end OpaquePricing.Dominance
