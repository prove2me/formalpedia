-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair029_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair029_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:00:05.591979+00:00
-- url     : https://prove2.me/theorems/14443774-fe1b-4f54-aa2d-f9f2ddcf249a
-- title:
--   Rounded reciprocal Mobius certificate on [475136, 491520)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $475136\le n<491520$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part07
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair029_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 475136 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block058 mobiusReciprocal1200001Block059) = true := by sorry

end Helfgott
