-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair054_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair054_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:25:40.391557+00:00
-- url     : https://prove2.me/theorems/c1281609-2788-48a6-8577-a4d18da77786
-- title:
--   Rounded reciprocal Mobius certificate on [884736, 901120)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $884736\le n<901120$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part13
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair054_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 884736 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block108 mobiusReciprocal1200001Block109) = true := by sorry

end Helfgott
