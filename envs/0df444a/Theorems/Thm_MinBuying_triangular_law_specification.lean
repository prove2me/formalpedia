-- Prove2me | Theorems.Thm_MinBuying_triangular_law_specification
-- name    : MinBuying.triangular_law_specification
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:20:05.620808+00:00
-- url     : https://prove2.me/theorems/92866e30-f5a2-469d-a666-e2067200ec5b
-- title:
--   Equations (11)–(12): triangular law and cap atom
-- statement:
--   For positive $a,v$, the explicitly constructed triangular law is a nonnegative probability law and is regular. Its strict rejection probabilities, right CDF, and cap atom agree with the source formulas; in particular $\Pr(V<v)=v/(v+a)$ whereas $\Pr(V\le v)=1$, and $\Pr(V=v)=a/(a+v)$.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . p.18, Eqs.(11)–(12).

import Definitions.Def_MinBuying_Triangular
import Definitions.Def_MinBuying_Regularity

open MeasureTheory Set

namespace MinBuying

/-- Distributional content of equations (11)--(12), including the cap atom.
This is a supporting obligation for the explicit pushforward definition. -/
theorem triangular_law_specification (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    ValidMarginal (triangularLaw a v) ∧
    Regular (triangularLaw a v) ∧
    (∀ p : ℝ, rejection (triangularLaw a v) p = triangularReject a v p) ∧
    (∀ p : ℝ, cdf (triangularLaw a v) p = triangularCDF a v p) ∧
    ((triangularLaw a v) {v}).toReal = a / (a + v) ∧
    (∀ᵐ x ∂triangularLaw a v, x ∈ Icc (0 : ℝ) v) := by
  sorry

end MinBuying
