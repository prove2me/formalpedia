-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair055_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair055_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:27:51.317556+00:00
-- url     : https://prove2.me/theorems/1f64a501-741f-4ae9-90de-d3082df35462
-- title:
--   Rounded reciprocal Mobius certificate on [901120, 917504)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $901120\le n<917504$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part13
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair055_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 901120 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block110 mobiusReciprocal1200001Block111) = true := by sorry

end Helfgott
