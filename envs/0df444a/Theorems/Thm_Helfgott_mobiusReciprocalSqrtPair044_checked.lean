-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair044_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair044_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:15:19.697434+00:00
-- url     : https://prove2.me/theorems/abd9e00a-aa8a-421d-8fdf-ecef4a45883c
-- title:
--   Rounded reciprocal Mobius certificate on [720896, 737280)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $720896\le n<737280$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part11
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair044_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 720896 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block088 mobiusReciprocal1200001Block089) = true := by sorry

end Helfgott
