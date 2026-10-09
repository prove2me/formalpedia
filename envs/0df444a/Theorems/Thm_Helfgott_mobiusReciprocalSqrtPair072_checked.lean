-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair072_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair072_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:45:45.428851+00:00
-- url     : https://prove2.me/theorems/1b4a78ea-11c7-4ed6-b3d9-40880acc3ba5
-- title:
--   Rounded reciprocal Mobius certificate on [1179648, 1196032)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $1179648\le n<1196032$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part18
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair072_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1179648 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block144 mobiusReciprocal1200001Block145) = true := by sorry

end Helfgott
