-- Prove2me | Theorems.Thm_MinBuying_triangular_cap_list_extraction
-- name    : MinBuying.triangular_cap_list_extraction
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:49:22.604995+00:00
-- url     : https://prove2.me/theorems/50b845eb-9bb3-44a5-8575-6aff05c4d2cc
-- title:
--   An ordered active-item list from an optimal triangular pricing policy
-- statement:
--   Let I be a positive-size triangular instance with optimal uniform revenue one. There is a list L of at most n positive triangular parameter pairs with weakly decreasing caps whose continuation from zero is at least the optimal differentiated revenue of I. For every t>0,
--
--   $$t\left[1-\prod_{(a,v)\in L}\Pr_{\operatorname{Tri}(a,v)}(V<t)\right]\le1.$$
--
--   This extracts the active items of a suitable cap-or-disabled policy and supplies an ordered algebraic representation for the canonical reduction. It does not assume that all items should remain active.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, proof of Lemma 2, electronic companion ec8–ec11. Auxiliary result proved for this formalization.

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- An optimal cap-or-disabled policy yields an ordered list of its active
triangular items without increasing any uniform revenue. -/
theorem triangular_cap_list_extraction (n : ℕ) (hn : 0 < n) (I : TriangularInstance n)
    (hNorm : UPRevenue (triangularJoint I) = 1) :
    ∃ L : List (ℝ × ℝ), L.length ≤ n ∧
      (∀ x ∈ L, 0 < x.1 ∧ 0 < x.2) ∧
      L.Pairwise (fun x y => y.2 ≤ x.2) ∧
      DPRevenue (triangularJoint I) ≤ L.foldl (fun C x => continuationStep x.1 x.2 C) 0 ∧
      (∀ t : ℝ, 0 < t → t * (1 - (L.map (fun x => triangularReject x.1 x.2 t)).prod) ≤ 1) := by
  sorry

end MinBuying
