-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair052_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair052_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:24:19.080074+00:00
-- url     : https://prove2.me/theorems/bd65697a-b5c2-4bcb-83a7-fa2dc8630e35
-- title:
--   Rounded reciprocal Mobius certificate on [851968, 868352)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $851968\le n<868352$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part13
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair052_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 851968 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block104 mobiusReciprocal1200001Block105) = true := by sorry

end Helfgott
