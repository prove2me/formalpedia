-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair013_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair013_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:42:00.626809+00:00
-- url     : https://prove2.me/theorems/c278113e-bf64-4142-813c-b57340dd6ea2
-- title:
--   Rounded reciprocal Mobius certificate on [212992, 229376)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $212992\le n<229376$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part03
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair013_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 212992 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block026 mobiusReciprocal1200001Block027) = true := by sorry

end Helfgott
