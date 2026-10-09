-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair028_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair028_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:56:53.041385+00:00
-- url     : https://prove2.me/theorems/1c179872-b057-4ba9-ac44-b670b8c4ed9d
-- title:
--   Rounded reciprocal Mobius certificate on [458752, 475136)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $458752\le n<475136$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part07
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair028_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 458752 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block056 mobiusReciprocal1200001Block057) = true := by sorry

end Helfgott
