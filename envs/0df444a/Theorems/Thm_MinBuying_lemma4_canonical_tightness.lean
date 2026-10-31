-- Prove2me | Theorems.Thm_MinBuying_lemma4_canonical_tightness
-- name    : MinBuying.lemma4_canonical_tightness
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:26:17.471405+00:00
-- url     : https://prove2.me/theorems/5aa36039-a00d-413f-9ca0-d6fc6abc75b6
-- title:
--   Lemma 4: finite canonical instances approach the bound
-- statement:
--   For every $\varepsilon>0$, there exists a finite canonical triangular instance with optimal uniform revenue exactly one and optimal differentiated revenue strictly greater than $1/x^\star-\varepsilon$. The finite item count may depend on $\varepsilon$.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . p.23, Lemma 4; PDF pp.42–44/ec15–ec17.

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- Lemma 4, PDF p.23, with the exact source conclusion in terms of optimal
differentiated revenue. The witness has finite attained positive optima. -/
theorem lemma4_canonical_tightness (ε : ℝ) (hε : 0 < ε) :
    ∃ I : CanonicalInstance,
      UPRevenue (canonicalLaw I) = 1 ∧
      1 / criticalRatio - ε < DPRevenue (canonicalLaw I) := by
  sorry

end MinBuying
