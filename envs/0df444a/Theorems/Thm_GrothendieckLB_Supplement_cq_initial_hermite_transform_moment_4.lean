-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_initial_hermite_transform_moment_4
-- name    : GrothendieckLB.Supplement.cq_initial_hermite_transform_moment_4
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T21:05:06.56226+00:00
-- url     : https://prove2.me/theorems/0fe1a1fb-a0bd-482a-987e-8baf7768c5c2
-- title:
--   Certified initial Hermite transform for the order-4 sextic seed
-- statement:
--   For every even spatial degree from 0 through 752, both recorded endpoints of the coefficient of the order-4 sextic seed equal the exact interval Hermite transform of the raw moments. After clearing the factorial denominators, the sum and the difference of the endpoints are ordinary one-dimensional integer convolutions.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.1. The monic Hermite expansion at the three independent sextic initial moments.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayMoments

namespace GrothendieckLB.Supplement

theorem cq_initial_hermite_transform_moment_4 :
    ∀ n < 377, (CQHeadCertificate.first (2*n)).e4 =
      (CQHeadArithmetic.sumCombinations (fun j => CQHeadArithmetic.scaleCombination
        (CQHeadCertificate.hc (2*n) j) (CQHeadCertificate.raw j)) (2*n+1)).e4 := by sorry

end GrothendieckLB.Supplement
