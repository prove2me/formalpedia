-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_initial_hermite_center_moment_2
-- name    : GrothendieckLB.Supplement.cq_initial_hermite_center_moment_2
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T21:17:46.712954+00:00
-- url     : https://prove2.me/theorems/f586f191-8345-4324-86ff-1753451012ba
-- title:
--   Signed Hermite midpoint transform for the order-2 seed
-- statement:
--   For all 377 even degrees, the sum of the recorded lower and upper endpoints of the order-2 seed component equals the corresponding signed Hermite transform. Clearing factorial denominators turns this into a single integer polynomial product.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.1. Signed and unsigned parts of the exact Hermite transform.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayMoments

namespace GrothendieckLB.Supplement

theorem cq_initial_hermite_center_moment_2 :
    ∀ n < 377, let x := (CQHeadCertificate.first (2*n)).e2
      let y := (CQHeadArithmetic.sumCombinations (fun j => CQHeadArithmetic.scaleCombination
        (CQHeadCertificate.hc (2*n) j) (CQHeadCertificate.raw j)) (2*n+1)).e2
      x.lo+x.hi=y.lo+y.hi := by sorry

end GrothendieckLB.Supplement
