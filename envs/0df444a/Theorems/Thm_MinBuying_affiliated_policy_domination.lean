-- Prove2me | Theorems.Thm_MinBuying_affiliated_policy_domination
-- name    : MinBuying.affiliated_policy_domination
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:18:19.876218+00:00
-- url     : https://prove2.me/theorems/92fe4da2-6478-4fff-aa64-011d1fa1e966
-- title:
--   Theorem 2 proof: uniform-price domination under affiliation
-- statement:
--   For every feasible price vector under an exchangeable affiliated nonnegative joint probability law with a positive finite number of coordinates, one of the coordinate prices earns weakly greater revenue when charged uniformly. This policy assertion uses no optimum-attainment assumption and covers the density-or-PMF affiliation scope of Definition 1.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . PDF pp.30–32/ec3–ec5, proof of Theorem 2.

import Definitions.Def_MinBuying_Symmetry

namespace MinBuying

/-- The stronger own-vector domination statement from the proof of Theorem 2
(ec3--ec5), formulated without assuming an optimizing vector is attained. -/
theorem affiliated_policy_domination (n : ℕ) (hn : 0 < n) (μ : JointLaw n)
    (hμ : ValidLaw μ) (hex : Exchangeable μ) (haff : Affiliated μ)
    (p : Prices n) (hp : FeasiblePrices p) :
    ∃ i : Fin n, Revenue μ p ≤ uniformRevenue μ (p i) := by
  sorry

end MinBuying
