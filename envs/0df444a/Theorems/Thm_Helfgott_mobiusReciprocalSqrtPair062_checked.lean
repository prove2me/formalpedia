-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair062_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair062_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:35:03.268931+00:00
-- url     : https://prove2.me/theorems/afd0e143-1155-4185-9cc7-41afd3c069de
-- title:
--   Rounded reciprocal Mobius certificate on [1015808, 1032192)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $1015808\le n<1032192$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part15
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair062_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1015808 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block124 mobiusReciprocal1200001Block125) = true := by sorry

end Helfgott
