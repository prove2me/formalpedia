-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_case_ii
-- name    : OpaquePricing.Dominance.case_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:05.067647+00:00
-- url     : https://prove2.me/theorems/b1e7fd59-4e06-4291-90b7-36270d541a2d
-- title:
--   Theorem 1, Case (ii): two-value opaque selling dominates DP
-- statement:
--   Let $N\ge2$ and let $F$ be an exchangeable probability law on nonnegative valuation vectors whose coordinates almost surely take only two common values. For any pessimistic-customer share $0\le\alpha\le1$,
--
--   $$R_{\mathrm{DP}}\le R_{\mathrm{OPQ}}^\alpha.$$
--
--   This is the second branch of Theorem 1, including purely risk-neutral customers.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), proof of Theorem 1, Case (ii), pp. 19–20

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance

theorem case_ii {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ0 : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hexch : Exchangeable μ)
    (htwo : TwoValued μ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    optDP μ ≤ optOPQ μ α := by sorry

end OpaquePricing.Dominance
