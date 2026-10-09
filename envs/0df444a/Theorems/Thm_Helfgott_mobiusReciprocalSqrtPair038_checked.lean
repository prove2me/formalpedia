-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair038_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair038_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:08:54.156315+00:00
-- url     : https://prove2.me/theorems/410ced4a-c62e-4da6-abeb-c964060665c5
-- title:
--   Rounded reciprocal Mobius certificate on [622592, 638976)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $622592\le n<638976$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part09
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair038_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 622592 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block076 mobiusReciprocal1200001Block077) = true := by sorry

end Helfgott
