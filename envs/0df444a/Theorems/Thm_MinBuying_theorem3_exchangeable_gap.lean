-- Prove2me | Theorems.Thm_MinBuying_theorem3_exchangeable_gap
-- name    : MinBuying.theorem3_exchangeable_gap
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:19:20.523434+00:00
-- url     : https://prove2.me/theorems/e8fbfaa6-81ad-4ed6-995d-473aff68c4d7
-- title:
--   Theorem 3: logarithmic exchangeable revenue gap
-- statement:
--   For every integer $n\ge1$, there is an exchangeable nonnegative joint valuation law with finite attained positive pricing optima such that $R_{\mathrm{DP}}\ge(3/32)\log(n)R_{\mathrm{UP}}$. The logarithm is natural. No density or independence condition is imposed on this existential law.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . p.15, Theorem 3; PDF pp.32–34/ec5–ec7.

import Definitions.Def_MinBuying_Symmetry

namespace MinBuying

/-- Theorem 3 (p.15), with the natural logarithm and the stated constant 3/32.
The source's construction is discrete, so absolute continuity is not imposed. -/
theorem theorem3_exchangeable_gap (n : ℕ) (hn : 0 < n) :
    ∃ μ : JointLaw n, ValidLaw μ ∧ Exchangeable μ ∧ WellPosed μ ∧
      (3 / 32 : ℝ) * Real.log (n : ℝ) * UPRevenue μ ≤ DPRevenue μ := by
  sorry

end MinBuying
