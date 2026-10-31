-- Prove2me | Theorems.Thm_MinBuying_theorem2_affiliated
-- name    : MinBuying.theorem2_affiliated
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:18:50.496342+00:00
-- url     : https://prove2.me/theorems/c1e5667f-b07a-4521-bdf2-3d3504ef5c17
-- title:
--   Theorem 2: uniform optimality under exchangeability and affiliation
-- statement:
--   For a positive finite number of min-buying products, an exchangeable affiliated nonnegative joint valuation law, and the source's finite attained optima with positive uniform revenue, optimal differentiated and uniform revenues coincide. Affiliation is represented by either an MTP2 joint density or an MTP2 probability mass function.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . p.13, Theorem 2; Definition 1 pp.12–13; standing conventions p.7.

import Definitions.Def_MinBuying_Symmetry

namespace MinBuying

/-- Theorem 2 (p.13). Affiliation covers the density and PMF alternatives of
Definition 1; the discrete case includes ties among valuation coordinates. -/
theorem theorem2_affiliated (n : ℕ) (hn : 0 < n) (μ : JointLaw n)
    (hμ : ValidLaw μ) (hex : Exchangeable μ) (haff : Affiliated μ)
    (hopt : WellPosed μ) :
    DPRevenue μ = UPRevenue μ := by
  sorry

end MinBuying
