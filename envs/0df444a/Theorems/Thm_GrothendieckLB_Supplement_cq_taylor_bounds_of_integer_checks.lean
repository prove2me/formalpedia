-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_taylor_bounds_of_integer_checks
-- name    : GrothendieckLB.Supplement.cq_taylor_bounds_of_integer_checks
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T19:51:55.111946+00:00
-- url     : https://prove2.me/theorems/1eef07d1-b84d-45a3-8451-3fa6b23fe4f1
-- title:
--   Soundness of partial integer certificates for the cubic–quintic Taylor coefficients
-- statement:
--   For every list of requested odd degrees through a cutoff $n\le251$, a successful integer interval check certifies the corresponding Taylor coefficients of the cubic–quintic Gaussian correlation. The same three starting integrals give a linear coefficient of at least $88157382204959954858/10^{20}$. The statement also applies to a single comparison or to disjoint lists of degrees.
-- source:
--   The fixed-point verifier of Prove2Me submission 6ced4b79-2df5-46cd-91cc-4b3d293f1114 for the cubic–quintic correlation of Saha et al., arXiv:2608.11158v2.

import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_cqHeadUnits
import Definitions.Def_GrothendieckLB_Supplement_cqNonlinearHeadCheck

namespace GrothendieckLB.Supplement

theorem cq_taylor_bounds_of_integer_checks {n : ℕ} (hn : n ≤ 251) (js : List ℕ)
    (hdeg : ∀ j ∈ js, 2*j+3 ≤ n) (hcheck : CQHeadArithmetic.verifyList n js = true) :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (88157382204959954858 : ℝ) / 10^20 ≤ GrothendieckLB.taylorCoeff 1 H ∧
      ∀ j ∈ js, |GrothendieckLB.taylorCoeff (2*j+3) H| ≤
        ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ) / 10^20 := by sorry

end GrothendieckLB.Supplement
