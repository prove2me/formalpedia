-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair059_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair059_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:32:43.445136+00:00
-- url     : https://prove2.me/theorems/b6fb5c93-7526-426d-a053-5b8a8a63e083
-- title:
--   Rounded reciprocal Mobius certificate on [966656, 983040)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $966656\le n<983040$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part14
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair059_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 966656 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block118 mobiusReciprocal1200001Block119) = true := by sorry

end Helfgott
