-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair046_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair046_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:17:23.024983+00:00
-- url     : https://prove2.me/theorems/9964dba2-6fe5-4b75-873e-7ee042e67849
-- title:
--   Rounded reciprocal Mobius certificate on [753664, 770048)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $753664\le n<770048$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part11
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair046_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 753664 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block092 mobiusReciprocal1200001Block093) = true := by sorry

end Helfgott
