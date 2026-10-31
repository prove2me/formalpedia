-- Prove2me | Theorems.Thm_MinBuying_lemmaEC1_rejection_bound
-- name    : MinBuying.lemmaEC1_rejection_bound
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:23:15.320264+00:00
-- url     : https://prove2.me/theorems/700366c4-8b70-4e45-a16e-dcec8de8f910
-- title:
--   Lemma EC.1: rejection probability bound
-- statement:
--   For a finite independent triangular family with positive parameters and weakly decreasing caps, and a common price $t>0$ no larger than any cap, let $C$ be the continuation revenue from pricing at the caps. Then $\prod_i t/(t+a_i)\le t/(t+C)$. The empty family is included with product one and continuation zero.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . PDF p.45/ec18, Lemma EC.1.

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- Lemma EC.1, PDF p.45: strict-rejection bound for decreasing-cap
triangular items. Includes the empty-product/zero-continuation base case. -/
theorem lemmaEC1_rejection_bound (n : ℕ) (I : TriangularInstance n)
    (hOrder : Antitone I.cap) (t : ℝ) (ht : 0 < t)
    (hCaps : ∀ i, t ≤ I.cap i) :
    triangularRejectionProduct I t ≤ t / (t + triangularContinuation I n) := by
  sorry

end MinBuying
