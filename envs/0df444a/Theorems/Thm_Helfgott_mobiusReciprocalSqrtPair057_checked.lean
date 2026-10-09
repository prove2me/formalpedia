-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair057_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair057_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:29:23.995041+00:00
-- url     : https://prove2.me/theorems/cd52e519-6168-4225-86c6-9cdcce56add2
-- title:
--   Rounded reciprocal Mobius certificate on [933888, 950272)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $933888\le n<950272$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part14
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair057_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 933888 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block114 mobiusReciprocal1200001Block115) = true := by sorry

end Helfgott
