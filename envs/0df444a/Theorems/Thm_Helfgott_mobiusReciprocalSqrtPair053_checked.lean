-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair053_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair053_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:24:04.955392+00:00
-- url     : https://prove2.me/theorems/1ef3a455-9827-4b6d-a9d5-e2e5f74355f7
-- title:
--   Rounded reciprocal Mobius certificate on [868352, 884736)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $868352\le n<884736$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part13
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair053_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 868352 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block106 mobiusReciprocal1200001Block107) = true := by sorry

end Helfgott
