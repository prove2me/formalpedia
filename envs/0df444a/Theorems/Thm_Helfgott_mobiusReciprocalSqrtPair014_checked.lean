-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair014_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair014_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:42:00.024854+00:00
-- url     : https://prove2.me/theorems/6f8c43dd-cb72-43f0-9bc1-ee9696e17f82
-- title:
--   Rounded reciprocal Mobius certificate on [229376, 245760)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $229376\le n<245760$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part03
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair014_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 229376 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block028 mobiusReciprocal1200001Block029) = true := by sorry

end Helfgott
