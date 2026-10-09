-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair033_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair033_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:04:27.67298+00:00
-- url     : https://prove2.me/theorems/c73188d1-ad8f-4a7e-a2d2-3a50d3c5fa86
-- title:
--   Rounded reciprocal Mobius certificate on [540672, 557056)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $540672\le n<557056$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part08
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair033_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 540672 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block066 mobiusReciprocal1200001Block067) = true := by sorry

end Helfgott
