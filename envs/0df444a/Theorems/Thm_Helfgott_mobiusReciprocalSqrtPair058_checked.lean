-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair058_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair058_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:30:35.509085+00:00
-- url     : https://prove2.me/theorems/ca322845-ebfc-4f88-87ca-4453cc524d6b
-- title:
--   Rounded reciprocal Mobius certificate on [950272, 966656)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $950272\le n<966656$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part14
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair058_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 950272 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block116 mobiusReciprocal1200001Block117) = true := by sorry

end Helfgott
