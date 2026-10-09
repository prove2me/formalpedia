-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair011_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair011_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:38:42.000962+00:00
-- url     : https://prove2.me/theorems/d2756046-9f00-4d1c-8995-7b19548c5c59
-- title:
--   Rounded reciprocal Mobius certificate on [180224, 196608)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $180224\le n<196608$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part02
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair011_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 180224 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block022 mobiusReciprocal1200001Block023) = true := by sorry

end Helfgott
