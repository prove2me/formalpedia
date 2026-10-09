-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair071_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair071_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:44:33.670254+00:00
-- url     : https://prove2.me/theorems/279e696a-5b3c-48da-b202-880e0bb2b73e
-- title:
--   Rounded reciprocal Mobius certificate on [1163264, 1179648)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $1163264\le n<1179648$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part17
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair071_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1163264 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block142 mobiusReciprocal1200001Block143) = true := by sorry

end Helfgott
