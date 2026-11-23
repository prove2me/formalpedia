-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_head_through_degree_17
-- name    : GrothendieckLB.Supplement.cq_head_through_degree_17
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T18:55:24.883095+00:00
-- url     : https://prove2.me/theorems/e8fb907c-e742-4637-bff7-3d777f0feeef
-- title:
--   Verified Taylor coefficient enclosures for the cubic–quintic scheme through degree 17
-- statement:
--   For the cubic–quintic correlation at the specified three decimal parameters, its linear Taylor coefficient is at least $88157382204959954858/10^{20}$. Its nonlinear Taylor coefficients at degrees $3,5,7,9,11,13,15,17$ satisfy the corresponding eight published upper bounds in absolute value. These are direct coefficient bounds for the Gaussian correlation, obtained by an integer interval computation at cutoff 17 and the proved integrated Hermite expansion.
-- source:
--   Saha et al., arXiv:2608.11158v2, cubic–quintic coefficient estimates. Smaller degree cutoff for the fixed-point verifier in Prove2Me submission 6ced4b79-2df5-46cd-91cc-4b3d293f1114.

import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_cqHeadUnits

namespace GrothendieckLB.Supplement

theorem cq_head_through_degree_17 :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (88157382204959954858 : ℝ) / 10 ^ 20 ≤ GrothendieckLB.taylorCoeff 1 H ∧
      ∀ j : ℕ, j < 8 →
        |GrothendieckLB.taylorCoeff (2 * j + 3) H| ≤
          ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ) / 10 ^ 20 := by sorry

end GrothendieckLB.Supplement
