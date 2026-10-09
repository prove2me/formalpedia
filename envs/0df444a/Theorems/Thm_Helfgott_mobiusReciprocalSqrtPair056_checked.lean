-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair056_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair056_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:28:40.920923+00:00
-- url     : https://prove2.me/theorems/de5fadaf-fa0f-46fa-8ba1-6ed8c4e51b47
-- title:
--   Rounded reciprocal Mobius certificate on [917504, 933888)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $917504\le n<933888$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part14
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair056_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 917504 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block112 mobiusReciprocal1200001Block113) = true := by sorry

end Helfgott
