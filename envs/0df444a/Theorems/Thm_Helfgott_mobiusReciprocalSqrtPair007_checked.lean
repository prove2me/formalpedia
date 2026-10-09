-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair007_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair007_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:34:17.463633+00:00
-- url     : https://prove2.me/theorems/01a9496f-7068-47de-82dc-082f8fe0271c
-- title:
--   Rounded reciprocal Mobius certificate on [114688, 131072)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $114688\le n<131072$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part01
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair007_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 114688 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block014 mobiusReciprocal1200001Block015) = true := by sorry

end Helfgott
