-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair020_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair020_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:48:39.189357+00:00
-- url     : https://prove2.me/theorems/709be9a8-0b2f-4a60-ac0d-37876ccbff11
-- title:
--   Rounded reciprocal Mobius certificate on [327680, 344064)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $327680\le n<344064$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part05
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair020_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 327680 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block040 mobiusReciprocal1200001Block041) = true := by sorry

end Helfgott
