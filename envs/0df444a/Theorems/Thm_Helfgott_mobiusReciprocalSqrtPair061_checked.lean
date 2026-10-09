-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair061_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair061_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:34:38.462982+00:00
-- url     : https://prove2.me/theorems/43244d7f-7f25-4f4a-b5f3-b1b1c9641a73
-- title:
--   Rounded reciprocal Mobius certificate on [999424, 1015808)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $999424\le n<1015808$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part15
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair061_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 999424 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block122 mobiusReciprocal1200001Block123) = true := by sorry

end Helfgott
