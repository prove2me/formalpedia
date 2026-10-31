-- Prove2me | Theorems.Thm_MinBuying_lemma2_canonical_reduction
-- name    : MinBuying.lemma2_canonical_reduction
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:24:42.254083+00:00
-- url     : https://prove2.me/theorems/64a6cd8a-68ac-429c-954f-777ffd8f3824
-- title:
--   Lemma 2: reduction to a canonical instance
-- statement:
--   For an independent triangular instance of $n\ge1$ products normalized to optimal uniform revenue one, and every $\varepsilon>0$, there exists a canonical instance with $N\le n$ additional items plus one terminal item. Its designated cap-pricing revenue is at least the original optimal differentiated revenue minus $\varepsilon$, and its optimal uniform revenue is at most one.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . p.20, Lemma 2; PDF pp.35–38/ec8–ec11.

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- Lemma 2, PDF p.20: normalized triangular instances admit canonical
cap-pricing approximations, with at most `n` nonterminal items. -/
theorem lemma2_canonical_reduction (n : ℕ) (hn : 0 < n)
    (I : TriangularInstance n) (hNorm : UPRevenue (triangularJoint I) = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : CanonicalInstance, J.count ≤ n ∧
      DPRevenue (triangularJoint I) - ε ≤
        Revenue (canonicalLaw J) (canonicalPrices J) ∧
      UPRevenue (canonicalLaw J) ≤ 1 := by
  sorry

end MinBuying
