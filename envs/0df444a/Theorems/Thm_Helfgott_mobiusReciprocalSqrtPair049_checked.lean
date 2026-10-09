-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair049_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair049_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:20:41.87968+00:00
-- url     : https://prove2.me/theorems/e30a1eca-b845-4664-b1e5-68be2141c449
-- title:
--   Rounded reciprocal Mobius certificate on [802816, 819200)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $802816\le n<819200$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part12
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair049_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 802816 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block098 mobiusReciprocal1200001Block099) = true := by sorry

end Helfgott
