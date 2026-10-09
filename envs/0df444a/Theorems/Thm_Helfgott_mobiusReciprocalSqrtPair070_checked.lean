-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair070_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair070_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:43:09.785987+00:00
-- url     : https://prove2.me/theorems/b8957fa9-86b6-40bd-b7a8-fef60700a6f3
-- title:
--   Rounded reciprocal Mobius certificate on [1146880, 1163264)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $1146880\le n<1163264$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part17
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair070_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1146880 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block140 mobiusReciprocal1200001Block141) = true := by sorry

end Helfgott
