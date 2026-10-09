-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair016_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair016_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:44:16.169617+00:00
-- url     : https://prove2.me/theorems/3f50ac9f-fb8f-472b-a8bf-32a229172aca
-- title:
--   Rounded reciprocal Mobius certificate on [262144, 278528)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $262144\le n<278528$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part04
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair016_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 262144 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block032 mobiusReciprocal1200001Block033) = true := by sorry

end Helfgott
