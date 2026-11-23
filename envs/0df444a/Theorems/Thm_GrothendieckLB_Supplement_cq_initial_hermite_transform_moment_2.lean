-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_initial_hermite_transform_moment_2
-- name    : GrothendieckLB.Supplement.cq_initial_hermite_transform_moment_2
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T21:04:52.130726+00:00
-- url     : https://prove2.me/theorems/66111f98-6f3f-4805-9406-919e6cf3c1f7
-- title:
--   Certified initial Hermite transform for the order-2 sextic seed
-- statement:
--   For every even spatial degree from 0 through 752, both recorded endpoints of the coefficient of the order-2 sextic seed equal the exact interval Hermite transform of the raw moments. After clearing the factorial denominators, the sum and the difference of the endpoints are ordinary one-dimensional integer convolutions.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.1. The monic Hermite expansion at the three independent sextic initial moments.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayMoments

namespace GrothendieckLB.Supplement

theorem cq_initial_hermite_transform_moment_2 :
    ∀ n < 377, (CQHeadCertificate.first (2*n)).e2 =
      (CQHeadArithmetic.sumCombinations (fun j => CQHeadArithmetic.scaleCombination
        (CQHeadCertificate.hc (2*n) j) (CQHeadCertificate.raw j)) (2*n+1)).e2 := by sorry

end GrothendieckLB.Supplement
