-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair050_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair050_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:21:07.437788+00:00
-- url     : https://prove2.me/theorems/74bcd9a5-e348-45ce-9de0-bed8a4c130b7
-- title:
--   Rounded reciprocal Mobius certificate on [819200, 835584)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $819200\le n<835584$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part12
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair050_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 819200 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block100 mobiusReciprocal1200001Block101) = true := by sorry

end Helfgott
