-- Prove2me | Theorems.Thm_MinBuying_theorem1_iid
-- name    : MinBuying.theorem1_iid
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:17:02.120966+00:00
-- url     : https://prove2.me/theorems/5d47e1c0-eaa6-4e94-8b3c-1a3e8c7f14b4
-- title:
--   Theorem 1: uniform optimality for IID valuations
-- statement:
--   For a positive finite number of min-buying products, IID strictly positive valuations with the source's absolutely continuous marginal convention and finite attained pricing optima with positive uniform revenue, optimal uniform pricing and differentiated pricing have equal revenue: $R_{\mathrm{DP}}=R_{\mathrm{UP}}$.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . p.10, Theorem 1; standing conventions p.7.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory

namespace MinBuying

/-- Theorem 1 (p.10), retaining the source's positive-valued marginal and
standing absolute-continuity and well-posedness assumptions. -/
theorem theorem1_iid (n : ℕ) (hn : 0 < n) (F : Measure ℝ)
    (hF : ValidMarginal F) (hpos : ∀ᵐ v ∂F, 0 < v)
    (hcont : F ≪ volume) (hopt : WellPosed (iidLaw n F)) :
    DPRevenue (iidLaw n F) = UPRevenue (iidLaw n F) := by
  sorry

end MinBuying
