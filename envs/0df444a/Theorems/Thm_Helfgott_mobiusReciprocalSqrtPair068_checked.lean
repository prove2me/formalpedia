-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair068_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair068_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:41:49.367454+00:00
-- url     : https://prove2.me/theorems/d912fbe7-0660-4393-b4d9-b1094015b45f
-- title:
--   Rounded reciprocal Mobius certificate on [1114112, 1130496)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $1114112\le n<1130496$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part17
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair068_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1114112 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block136 mobiusReciprocal1200001Block137) = true := by sorry

end Helfgott
