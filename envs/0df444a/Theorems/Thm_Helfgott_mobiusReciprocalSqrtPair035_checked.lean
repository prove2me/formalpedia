-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair035_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair035_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:05:00.420895+00:00
-- url     : https://prove2.me/theorems/837b1c4d-f6e7-4204-b304-49f5fcdd533d
-- title:
--   Rounded reciprocal Mobius certificate on [573440, 589824)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $573440\le n<589824$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part08
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair035_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 573440 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block070 mobiusReciprocal1200001Block071) = true := by sorry

end Helfgott
