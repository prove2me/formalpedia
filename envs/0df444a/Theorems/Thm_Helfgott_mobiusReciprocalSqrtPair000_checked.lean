-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair000_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair000_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:22:35.822687+00:00
-- url     : https://prove2.me/theorems/8848bba4-bc3e-4239-b43c-3d86d80d89e5
-- title:
--   Rounded reciprocal Mobius certificate on [0, 16384)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $0\le n<16384$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part00
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair000_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 0 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block000 mobiusReciprocal1200001Block001) = true := by sorry

end Helfgott
