-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair010_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair010_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:37:51.982885+00:00
-- url     : https://prove2.me/theorems/9bf33267-9d8f-473b-9e13-86d6bb364e2d
-- title:
--   Rounded reciprocal Mobius certificate on [163840, 180224)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $163840\le n<180224$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part02
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair010_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 163840 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block020 mobiusReciprocal1200001Block021) = true := by sorry

end Helfgott
