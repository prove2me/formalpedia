-- Prove2me | Theorems.Thm_MinBuying_triangular_revenue_homogeneity
-- name    : MinBuying.triangular_revenue_homogeneity
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:08:37.295349+00:00
-- url     : https://prove2.me/theorems/92dcbb36-6fc1-408c-809f-9dff450d2f8e
-- title:
--   Positive scaling of triangular min-buying revenues
-- statement:
--   Let $I$ be a finite independent triangular-valuation instance with parameters $a_i>0$ and caps $v_i>0$. Assume its differentiated and uniform revenue optima are finite and attained, with positive uniform optimum. For every scale $s>0$, there is an instance $J$ with the same number of items and parameters $s a_i$ and $s v_i$ such that the same optimization conditions hold and
--
--   $$R_{\mathrm{DP}}(J)=sR_{\mathrm{DP}}(I),\qquad R_{\mathrm{UP}}(J)=sR_{\mathrm{UP}}(I).$$
--
--   This formalizes the positive rescaling used to normalize uniform revenue to one in the proof of Theorem 4. It preserves the pricing ratio and does not add moment assumptions.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, p.23, proof of Theorem 4 (rescaling step); Eq.(11) for the triangular laws. Supporting normalization lemma.

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- Positive scaling of triangular valuation parameters scales both pricing
optima by the same factor. This is the normalization used on pp.22--23. -/
theorem triangular_revenue_homogeneity (n : ℕ) (I : TriangularInstance n)
    (hI : WellPosed (triangularJoint I)) (s : ℝ) (hs : 0 < s) :
    ∃ J : TriangularInstance n,
      (∀ i, J.a i = s * I.a i) ∧
      (∀ i, J.cap i = s * I.cap i) ∧
      WellPosed (triangularJoint J) ∧
      DPRevenue (triangularJoint J) = s * DPRevenue (triangularJoint I) ∧
      UPRevenue (triangularJoint J) = s * UPRevenue (triangularJoint I) := by
  sorry

end MinBuying
