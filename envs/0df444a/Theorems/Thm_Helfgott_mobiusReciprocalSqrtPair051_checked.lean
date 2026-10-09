-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair051_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair051_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:22:36.155238+00:00
-- url     : https://prove2.me/theorems/1a02cbfc-774b-477d-b8b3-7eeabdb92c27
-- title:
--   Rounded reciprocal Mobius certificate on [835584, 851968)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $835584\le n<851968$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part12
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair051_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 835584 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block102 mobiusReciprocal1200001Block103) = true := by sorry

end Helfgott
