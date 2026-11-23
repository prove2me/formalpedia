-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_fifth_price_majorant_quarters
-- name    : GrothendieckLB.Supplement.cq_fifth_price_majorant_quarters
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T21:03:51.685803+00:00
-- url     : https://prove2.me/theorems/83626e1c-d99b-47f6-9cf7-95363d26f088
-- title:
--   Four numerical bounds for the explicit fifth Gaussian majorant
-- statement:
--   For the rational chart in the first quadrant and the full closed-open radial interval, the explicitly specified real majorant, multiplied by $2.55$, satisfies the four stated upper bounds on successive quarter intervals.
-- source:
--   Independent Price differentiation and rational interval certificate for Saha et al., arXiv:2608.11158v2. The density identity is Prove2Me bb4bfdfc-4dcc-425d-8a98-1b646de8d12b.

import Mathlib
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_cqPriceMajorant

namespace GrothendieckLB.Supplement

theorem cq_fifth_price_majorant_quarters (r s : ℝ) (hr : (99999 : ℝ)/100000 ≤ r) (hr₁ : r < 1) (hs : s∈Set.Icc 0 1) :
    let u := (2.55 : ℝ) * CQPrice.majorant (CQPrice.point r s)
    (s ≤ 1/4 → u ≤ 531000) ∧
      (1/4 ≤ s → s ≤ 1/2 → u ≤ 545000) ∧
      (1/2 ≤ s → s ≤ 3/4 → u ≤ 486000) ∧
      (3/4 ≤ s → u ≤ 84000) := by sorry

end GrothendieckLB.Supplement
