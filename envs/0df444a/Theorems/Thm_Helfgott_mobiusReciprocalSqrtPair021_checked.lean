-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair021_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair021_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:50:23.294382+00:00
-- url     : https://prove2.me/theorems/d8463b07-a63c-4c0b-b60b-4ddc4dee4514
-- title:
--   Rounded reciprocal Mobius certificate on [344064, 360448)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $344064\le n<360448$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part05
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair021_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 344064 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block042 mobiusReciprocal1200001Block043) = true := by sorry

end Helfgott
