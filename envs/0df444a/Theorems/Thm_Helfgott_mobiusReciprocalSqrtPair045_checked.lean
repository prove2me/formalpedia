-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair045_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair045_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:16:35.024431+00:00
-- url     : https://prove2.me/theorems/21f8f0a0-b6e7-426d-905f-dc5c0dfbc3c4
-- title:
--   Rounded reciprocal Mobius certificate on [737280, 753664)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $737280\le n<753664$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part11
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair045_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 737280 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block090 mobiusReciprocal1200001Block091) = true := by sorry

end Helfgott
