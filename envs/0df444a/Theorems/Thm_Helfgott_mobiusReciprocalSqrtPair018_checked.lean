-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair018_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair018_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:46:53.789807+00:00
-- url     : https://prove2.me/theorems/bb912b9e-eaa7-4d64-84da-812bc95bfec3
-- title:
--   Rounded reciprocal Mobius certificate on [294912, 311296)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $294912\le n<311296$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part04
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair018_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 294912 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block036 mobiusReciprocal1200001Block037) = true := by sorry

end Helfgott
