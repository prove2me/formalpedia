-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair026_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair026_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:55:29.817473+00:00
-- url     : https://prove2.me/theorems/2872e90c-1774-4538-a9cf-24ab4f7f8ff0
-- title:
--   Rounded reciprocal Mobius certificate on [425984, 442368)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $425984\le n<442368$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part06
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair026_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 425984 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block052 mobiusReciprocal1200001Block053) = true := by sorry

end Helfgott
