-- Prove2me | Theorems.Thm_Light_Sec3_ChanHe_claim_CH20_Theorem_5_1
-- name    : Light.Sec3.ChanHe.claim_CH20_Theorem_5_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T15:39:10.446983+00:00
-- url     : https://prove2.me/theorems/2a0ed1b3-5b05-489c-a2e4-ea8dcdc4c089
-- title:
--   Deterministic 3SUM reduction to Convolution-3SUM (Chan and He)
-- statement:
--   For every fixed exponent $\kappa\ge0$, 3SUM on $n$ integers of absolute value at most $n^\kappa$ reduces deterministically to Convolution-3SUM using $n^{3/2}(\log n)^{O(1)}$ additional time, $(\log n)^{O(1)}$ oracle calls, and instances of length $n(\log n)^{O(1)}$ with polynomially bounded integers. The reduction is implemented in the light programming language with verified correctness, running time, and resource bounds.
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Program.lean#L153-L155

import Definitions.Def_ThreeSumSource_ReductionClaims
import Definitions.Def_APSPSource_RemainingDefinitions
set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem Light.Sec3.ChanHe.claim_CH20_Theorem_5_1 : ThreeSumApsp.Claim.CH20_Theorem_5_1 Light.lightModel := by sorry
