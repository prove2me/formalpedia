-- Prove2me | Theorems.Thm_MinBuying_affiliated_coordinate_threshold
-- name    : MinBuying.affiliated_coordinate_threshold
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:08:50.724606+00:00
-- url     : https://prove2.me/theorems/5f7a55f0-c1bb-4b81-b8ea-711a92ce3de5
-- title:
--   Coordinate-threshold comparison for affiliated laws
-- statement:
--   Let $V\in\mathbb R_+^n$ have an affiliated probability law represented either by a measurable nonnegative MTP2 Lebesgue density or by an MTP2 probability mass function. For any coordinates $i,j$ and real thresholds $a,s,t$ with $s\le t$,
--   $$\Pr(V_i<a,V_j\ge t)\Pr(V_j\ge s)\le\Pr(V_i<a,V_j\ge s)\Pr(V_j\ge t).$$
--   This cross-product form requires neither exchangeability nor positive conditioning probabilities. When both tail probabilities are positive, it compares the conditional probabilities of a low value in coordinate $i$ at the two thresholds on coordinate $j$.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133 . Supporting lemma for the proof of Theorem 2, ec2–ec3.

import Definitions.Def_MinBuying_Symmetry

namespace MinBuying

/-- A coordinate is stochastically increasing when another coordinate is
conditioned to exceed a higher threshold. The cross-product form also covers
zero-probability conditioning events. -/
theorem affiliated_coordinate_threshold (n : ℕ) (μ : JointLaw n)
    (hμ : ValidLaw μ) (haff : Affiliated μ) (i j : Fin n)
    (a s t : ℝ) (hst : s ≤ t) :
    (μ {v | v i < a ∧ t ≤ v j}).toReal * (μ {v | s ≤ v j}).toReal ≤
      (μ {v | v i < a ∧ s ≤ v j}).toReal * (μ {v | t ≤ v j}).toReal := by
  sorry

end MinBuying
