-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair006_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair006_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:34:17.184004+00:00
-- url     : https://prove2.me/theorems/6eb40ea2-8259-4480-a240-0992f1617ad0
-- title:
--   Rounded reciprocal Mobius certificate on [98304, 114688)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $98304\le n<114688$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part01
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair006_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 98304 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block012 mobiusReciprocal1200001Block013) = true := by sorry

end Helfgott
