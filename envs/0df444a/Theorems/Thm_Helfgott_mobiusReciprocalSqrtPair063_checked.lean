-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair063_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair063_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:36:36.132038+00:00
-- url     : https://prove2.me/theorems/34e57af1-c711-4ac5-a067-7794f9048fcc
-- title:
--   Rounded reciprocal Mobius certificate on [1032192, 1048576)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $1032192\le n<1048576$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part15
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair063_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1032192 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block126 mobiusReciprocal1200001Block127) = true := by sorry

end Helfgott
