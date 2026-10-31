-- Prove2me | Theorems.Thm_MinBuying_independent_revenue_formula
-- name    : MinBuying.independent_revenue_formula
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:15:50.182283+00:00
-- url     : https://prove2.me/theorems/0c9389c9-b861-4827-b2a5-0b62d9f98237
-- title:
--   Equations (1)–(2): independent min-buying revenues
-- statement:
--   For independent nonnegative valuation laws and a feasible price vector sorted in ascending order, expected min-buying revenue equals $\sum_i p_i(1-F_i^<(p_i))\prod_{j<i}F_j^<(p_j)$, where $F_i^<(t)=\Pr(V_i<t)$. Every nonnegative common price $q$ earns $q(1-\prod_iF_i^<(q))$. Strict rejection makes these identities valid at atoms.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . pp.8–9, Eqs.(1)–(2).

import Definitions.Def_MinBuying_Model

open MeasureTheory
open scoped BigOperators

namespace MinBuying

/-- Equations (1)--(2), written with strict rejection so they also cover
cap atoms. The formula for differentiated prices uses ascending price order. -/
theorem independent_revenue_formula (n : ℕ) (hn : 0 < n)
    (F : Fin n → Measure ℝ) (hF : ∀ i, ValidMarginal (F i))
    (p : Prices n) (hp : FeasiblePrices p) (hsorted : Monotone p) :
    Revenue (productLaw F) p = independentRevenueFormula F p ∧
    (∀ q : ℝ, 0 ≤ q →
      uniformRevenue (productLaw F) q = q * (1 - ∏ i : Fin n, rejection (F i) q)) := by
  sorry

end MinBuying
