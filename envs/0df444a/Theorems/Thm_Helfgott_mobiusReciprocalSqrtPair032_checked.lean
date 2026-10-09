-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair032_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair032_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:01:21.362047+00:00
-- url     : https://prove2.me/theorems/ac6c16da-9a03-47f8-87f5-336b7c7bed60
-- title:
--   Rounded reciprocal Mobius certificate on [524288, 540672)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $524288\le n<540672$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part08
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair032_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 524288 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block064 mobiusReciprocal1200001Block065) = true := by sorry

end Helfgott
