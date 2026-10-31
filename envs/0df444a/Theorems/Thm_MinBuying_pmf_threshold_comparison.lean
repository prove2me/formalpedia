-- Prove2me | Theorems.Thm_MinBuying_pmf_threshold_comparison
-- name    : MinBuying.pmf_threshold_comparison
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:08:50.549059+00:00
-- url     : https://prove2.me/theorems/31c8bdc0-c382-429f-a8f6-a2721a18a8b2
-- title:
--   Exchangeable affiliated PMF threshold comparison
-- statement:
--   Let $V\in\mathbb R_+^n$ have an exchangeable MTP2 probability mass function, where $n>0$. Fix any coordinate $i$ and thresholds $a\le b$, and suppose $\Pr(\max_j V_j\ge b)>0$. Then
--   $$\Pr(V_i<a\mid\max_j V_j\ge b)\le\Pr(V_i<a\mid\max_j V_j\ge a).$$
--   The second conditioning event also has positive probability. The result provides the threshold comparison used to eliminate differentiated prices and allows countably infinite support.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133 . Supporting lemma for the proof of Theorem 2, ec2–ec3.

import Definitions.Def_MinBuying_Symmetry

namespace MinBuying

/-- The exchangeable threshold comparison for a genuine probability mass
function, with no finite-support assumption. -/
theorem pmf_threshold_comparison (n : ℕ) (hn : 0 < n) (w : PMF (Valuations n))
    (hμ : ValidLaw w.toMeasure) (hex : Exchangeable w.toMeasure)
    (hmtp : MTP2 (fun v => (w v).toReal)) (i : Fin n) (a b : ℝ) (hab : a ≤ b)
    (hb : 0 < w.toMeasure (upperMaximumEvent b)) :
    (w.toMeasure (coordinateBelowAndUpperMaximumEvent i a b)).toReal /
        (w.toMeasure (upperMaximumEvent b)).toReal ≤
      (w.toMeasure (coordinateBelowAndUpperMaximumEvent i a a)).toReal /
        (w.toMeasure (upperMaximumEvent a)).toReal := by
  sorry

end MinBuying
