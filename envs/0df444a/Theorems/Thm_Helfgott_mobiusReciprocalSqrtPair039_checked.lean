-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair039_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair039_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:09:17.066352+00:00
-- url     : https://prove2.me/theorems/1672585d-47d1-4a2b-b86c-9a1c0f265592
-- title:
--   Rounded reciprocal Mobius certificate on [638976, 655360)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $638976\le n<655360$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part09
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair039_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 638976 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block078 mobiusReciprocal1200001Block079) = true := by sorry

end Helfgott
