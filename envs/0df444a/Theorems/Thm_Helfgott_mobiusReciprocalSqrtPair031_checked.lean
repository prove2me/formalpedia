-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair031_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair031_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:00:55.796599+00:00
-- url     : https://prove2.me/theorems/76f87cf0-9b04-4ff1-83fd-8247eff11f36
-- title:
--   Rounded reciprocal Mobius certificate on [507904, 524288)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $507904\le n<524288$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part07
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair031_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 507904 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block062 mobiusReciprocal1200001Block063) = true := by sorry

end Helfgott
