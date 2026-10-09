-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair001_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair001_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:29:31.219661+00:00
-- url     : https://prove2.me/theorems/1ca734f0-48bd-435f-b61d-91e598dfbde1
-- title:
--   Rounded reciprocal Mobius certificate on [16384, 32768)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $16384\le n<32768$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part00
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair001_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 16384 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block002 mobiusReciprocal1200001Block003) = true := by sorry

end Helfgott
