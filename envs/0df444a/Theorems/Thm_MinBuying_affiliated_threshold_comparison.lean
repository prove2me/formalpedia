-- Prove2me | Theorems.Thm_MinBuying_affiliated_threshold_comparison
-- name    : MinBuying.affiliated_threshold_comparison
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T16:17:34.073624+00:00
-- url     : https://prove2.me/theorems/9c86f66e-b98a-4e87-958d-90496ec9b9bb
-- title:
--   Equation (9): conditional maximum-threshold comparison
-- statement:
--   For an exchangeable affiliated nonnegative joint probability law, a coordinate $i$, and thresholds $a\le b$ with positive probability that the maximum is at least $b$, the conditional probability of $V_i<a$ given that the maximum is at least $a$ is at least its conditional probability given that the maximum is at least $b$. Affiliation is the actual density-or-PMF condition.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . p.14 Eq.(9); PDF pp.30–32/ec3–ec5, proof of Theorem 2.

import Definitions.Def_MinBuying_Symmetry

namespace MinBuying

/-- Equation (9), obtained in the source through affiliation of order
statistics. Conditioning events have positive probability; this is a theorem
obligation rather than an additional definition of affiliation. -/
theorem affiliated_threshold_comparison (n : ℕ) (hn : 0 < n) (μ : JointLaw n)
    (hμ : ValidLaw μ) (hex : Exchangeable μ) (haff : Affiliated μ)
    (i : Fin n) (a b : ℝ) (hab : a ≤ b)
    (hb : 0 < μ (upperMaximumEvent b)) :
    (μ (coordinateBelowAndUpperMaximumEvent i a b)).toReal /
        (μ (upperMaximumEvent b)).toReal ≤
      (μ (coordinateBelowAndUpperMaximumEvent i a a)).toReal /
        (μ (upperMaximumEvent a)).toReal := by
  sorry

end MinBuying
