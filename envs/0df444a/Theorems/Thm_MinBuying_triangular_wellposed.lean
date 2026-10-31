-- Prove2me | Theorems.Thm_MinBuying_triangular_wellposed
-- name    : MinBuying.triangular_wellposed
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:26:31.111987+00:00
-- url     : https://prove2.me/theorems/fd29cafb-7fe7-48af-b9ce-7e39df9b579f
-- title:
--   Finite attained optima for positive triangular markets
-- statement:
--   Every finite positive-size market with independent triangular valuation laws of positive parameters and caps is a valid nonnegative probability model. Its differentiated and uniform pricing revenue sets are bounded above, both optimal values are attained by nonnegative prices, and
--
--   $$R_{\mathrm{UP}}>0.$$
--
--   This establishes the optimization conventions required when triangular instances are introduced in the reductions, including the existence of actual optimizing price vectors.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, p.7, standing pricing-optimum conventions; pp.18–19, triangular valuation model, equations (11)–(13). Supporting finite-market attainment result.

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- Every positive-size triangular market has finite attained pricing optima
and strictly positive optimal uniform revenue. -/
theorem triangular_wellposed (n : ℕ) (hn : 0 < n) (I : TriangularInstance n) :
    ValidLaw (triangularJoint I) ∧ WellPosed (triangularJoint I) := by
  sorry

end MinBuying
