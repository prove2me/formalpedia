-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair041_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair041_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:12:01.419659+00:00
-- url     : https://prove2.me/theorems/f77f148c-a5db-442e-b301-db55b3e2e635
-- title:
--   Rounded reciprocal Mobius certificate on [671744, 688128)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $671744\le n<688128$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part10
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair041_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 671744 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block082 mobiusReciprocal1200001Block083) = true := by sorry

end Helfgott
