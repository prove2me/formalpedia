-- Prove2me | Theorems.Thm_Light_Sec3_claim_VW13_Theorem_4_3
-- name    : Light.Sec3.claim_VW13_Theorem_4_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T15:50:17.89979+00:00
-- url     : https://prove2.me/theorems/4222e112-fa83-41cc-89f8-42d0d6244d6b
-- title:
--   Convolution-3SUM from Exact Triangle on a deterministic machine
-- statement:
--   A deterministic Exact Triangle solver yields a Convolution-3SUM solver using \(O(\sqrt{N})\) triangle instances of size \(O(\sqrt{N})\), with bounded weights and \(N^{3/2+o(1)}\) additional work. This is the source formalization of the reduction used in Theorem 21(a), cited as [VW13, Theorem 4.3].
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/TimeBound.lean#L93-L100

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_ThreeSumSource_ReductionClaims
set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem Light.Sec3.claim_VW13_Theorem_4_3 : ThreeSumApsp.Claim.VW13_Theorem_4_3 Light.lightModel := by sorry
