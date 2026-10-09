-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair017_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair017_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:46:09.039294+00:00
-- url     : https://prove2.me/theorems/f825be2e-b71f-4fa0-ab1d-bb29cbea1539
-- title:
--   Rounded reciprocal Mobius certificate on [278528, 294912)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $278528\le n<294912$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part04
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair017_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 278528 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block034 mobiusReciprocal1200001Block035) = true := by sorry

end Helfgott
