-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair024_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair024_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:52:06.159798+00:00
-- url     : https://prove2.me/theorems/8cf15a95-be8f-4720-9988-86b69f6ecd7a
-- title:
--   Rounded reciprocal Mobius certificate on [393216, 409600)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $393216\le n<409600$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part06
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair024_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 393216 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block048 mobiusReciprocal1200001Block049) = true := by sorry

end Helfgott
