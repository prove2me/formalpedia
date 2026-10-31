-- Prove2me | Theorems.Thm_MinBuying_lemma1_triangular_reduction
-- name    : MinBuying.lemma1_triangular_reduction
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:23:57.397823+00:00
-- url     : https://prove2.me/theorems/e98ada8a-7405-48d7-b013-ce6f5ed77e3a
-- title:
--   Lemma 1: reduction to triangular-revenue distributions
-- statement:
--   Every positive-size independent continuous regular instance admits a family of at most the original number of independent positive-parameter triangular laws whose optimal differentiated revenue is weakly larger and whose optimal uniform revenue is weakly smaller. No interior acceptance-probability restriction is added.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . p.18, Lemma 1; PDF pp.34–35/ec7–ec8.

import Definitions.Def_MinBuying_Triangular
import Definitions.Def_MinBuying_Regularity

open MeasureTheory

namespace MinBuying

/-- Lemma 1, PDF p.18: reduce a continuous regular independent instance to
at most the original number of triangular-revenue items. The original
source's finite attained optima are included in `RegularInstance`. -/
theorem lemma1_triangular_reduction (n : ℕ) (F : Fin n → Measure ℝ)
    (hF : RegularInstance F) :
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ ∃ I : TriangularInstance m,
      WellPosed (triangularJoint I) ∧
      DPRevenue (productLaw F) ≤ DPRevenue (triangularJoint I) ∧
      UPRevenue (triangularJoint I) ≤ UPRevenue (productLaw F) := by
  sorry

end MinBuying
