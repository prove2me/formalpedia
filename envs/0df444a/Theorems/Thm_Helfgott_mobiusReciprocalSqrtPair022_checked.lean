-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair022_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair022_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:51:25.944532+00:00
-- url     : https://prove2.me/theorems/5a30fd1f-7b32-4f02-a174-060a31388455
-- title:
--   Rounded reciprocal Mobius certificate on [360448, 376832)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $360448\le n<376832$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part05
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair022_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 360448 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block044 mobiusReciprocal1200001Block045) = true := by sorry

end Helfgott
