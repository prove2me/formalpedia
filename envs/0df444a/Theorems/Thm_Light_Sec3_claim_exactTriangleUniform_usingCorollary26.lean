-- Prove2me | Theorems.Thm_Light_Sec3_claim_exactTriangleUniform_usingCorollary26
-- name    : Light.Sec3.claim_exactTriangleUniform_usingCorollary26
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T15:34:51.286694+00:00
-- url     : https://prove2.me/theorems/8cb71a10-1d07-4113-82bc-abeb4c6d4dc8
-- title:
--   Uniform Exact Triangle bound from Corollary 26
-- statement:
--   There is a constant \(K \ge 1\) such that a deterministic program in the source light language solves Exact Triangle with \(s\) vertices per part and integer edge weights of absolute value at most \(U\) within the uniform running-time bound
--   \[ K s^{3-0.00175}(\log s+1)(1+\log\max\{2,U\})^2, \]
--   for every \(s \ge 1\) and \(U \ge 1\). This is the strengthened Theorem 19 bound derived from Corollary 26. It supplies the shared algorithmic input for the 3SUM and APSP reductions.
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean#L57-L61

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSumApsp

theorem Light.Sec3.claim_exactTriangleUniform_usingCorollary26 :
    Claim.ExactTriangleUniform lightModel 0.00175 1:= by sorry
