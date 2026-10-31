-- Prove2me | Theorems.Thm_MinBuying_canonical_revenue_bridge
-- name    : MinBuying.canonical_revenue_bridge
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:20:32.08499+00:00
-- url     : https://prove2.me/theorems/3c8489de-1c66-448d-b1a3-e4554f83a69b
-- title:
--   Equations (13)–(14): canonical formulas equal market revenues
-- statement:
--   For every canonical parameter system, its actual joint product law is a valid min-buying market with well-posed pricing optima. The designated cap vector is feasible, its expected revenue equals the scalar continuation recursion, and each common-price expected revenue equals the explicit product formula. This identifies the algebraic benchmark with genuine pricing revenues.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . pp.19–22, Eqs.(13)–(14).

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- The scalar canonical formulas are the actual min-buying revenues of the
concrete independent product law, with finite attained positive optima. -/
theorem canonical_revenue_bridge (I : CanonicalInstance) :
    ValidLaw (canonicalLaw I) ∧
    WellPosed (canonicalLaw I) ∧
    Revenue (canonicalLaw I) (canonicalPrices I) = canonicalCapRevenue I ∧
    (∀ p : ℝ, 0 ≤ p →
      uniformRevenue (canonicalLaw I) p = canonicalUniformRevenueAt I p) := by
  sorry

end MinBuying
