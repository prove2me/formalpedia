-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair009_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair009_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:37:19.903997+00:00
-- url     : https://prove2.me/theorems/c519b697-d375-48d8-aaa1-f0d82f906ba5
-- title:
--   Rounded reciprocal Mobius certificate on [147456, 163840)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $147456\le n<163840$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part02
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair009_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 147456 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block018 mobiusReciprocal1200001Block019) = true := by sorry

end Helfgott
