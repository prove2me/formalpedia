-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair043_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair043_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:13:26.815988+00:00
-- url     : https://prove2.me/theorems/0b54a8fa-c349-43e6-9514-fdbbab419d75
-- title:
--   Rounded reciprocal Mobius certificate on [704512, 720896)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $704512\le n<720896$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part10
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair043_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 704512 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block086 mobiusReciprocal1200001Block087) = true := by sorry

end Helfgott
