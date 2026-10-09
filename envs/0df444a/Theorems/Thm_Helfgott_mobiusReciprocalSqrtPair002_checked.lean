-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair002_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair002_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:29:38.68161+00:00
-- url     : https://prove2.me/theorems/7bff002a-31dc-473f-b868-8a0fb02e02d9
-- title:
--   Rounded reciprocal Mobius certificate on [32768, 49152)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $32768\le n<49152$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part00
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair002_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 32768 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block004 mobiusReciprocal1200001Block005) = true := by sorry

end Helfgott
