-- Prove2me | Theorems.Thm_MinBuying_iid_policy_domination
-- name    : MinBuying.iid_policy_domination
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:16:30.796986+00:00
-- url     : https://prove2.me/theorems/a061e9ff-a00c-4acb-86f2-b11da25a33d1
-- title:
--   Theorem 1 proof: a price from the original vector dominates
-- statement:
--   For a positive finite item count, IID nonnegative probability valuations, and every feasible price vector $p$, there is a coordinate $i$ such that uniform pricing at $p_i$ earns at least the revenue of $p$. This is the stronger policy-level assertion explicitly proved in Theorem 1's induction and does not require optimizing-price attainment or regularity.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . pp.10–11, proof of Theorem 1, Eqs.(6)–(7); Note 1 p.24.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory

namespace MinBuying

/-- The stronger statement explicitly proved in Theorem 1: a uniform price
chosen from the original vector dominates it. The proof also permits atoms
and zero valuations, and does not require attained optimizing prices. -/
theorem iid_policy_domination (n : ℕ) (hn : 0 < n) (F : Measure ℝ)
    (hF : ValidMarginal F) (p : Prices n) (hp : FeasiblePrices p) :
    ∃ i : Fin n, Revenue (iidLaw n F) p ≤ uniformRevenue (iidLaw n F) (p i) := by
  sorry

end MinBuying
