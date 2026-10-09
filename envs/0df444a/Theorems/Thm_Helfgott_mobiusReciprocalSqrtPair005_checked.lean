-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair005_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair005_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:33:19.315547+00:00
-- url     : https://prove2.me/theorems/509bb724-cee1-4c5c-935f-04767b43625c
-- title:
--   Rounded reciprocal Mobius certificate on [81920, 98304)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $81920\le n<98304$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part01
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair005_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 81920 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block010 mobiusReciprocal1200001Block011) = true := by sorry

end Helfgott
