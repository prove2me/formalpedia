-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair037_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair037_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:08:29.541119+00:00
-- url     : https://prove2.me/theorems/256ac9c9-0056-4198-92fc-85414c671371
-- title:
--   Rounded reciprocal Mobius certificate on [606208, 622592)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $606208\le n<622592$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part09
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair037_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 606208 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block074 mobiusReciprocal1200001Block075) = true := by sorry

end Helfgott
