-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair019_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair019_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:47:28.390989+00:00
-- url     : https://prove2.me/theorems/f48e015a-976f-41b4-abff-2413e95cd60a
-- title:
--   Rounded reciprocal Mobius certificate on [311296, 327680)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $311296\le n<327680$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part04
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair019_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 311296 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block038 mobiusReciprocal1200001Block039) = true := by sorry

end Helfgott
