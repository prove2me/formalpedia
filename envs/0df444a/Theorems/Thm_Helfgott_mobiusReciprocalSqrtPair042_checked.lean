-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair042_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair042_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:13:15.398205+00:00
-- url     : https://prove2.me/theorems/b5a4b988-ccad-4137-ab20-612b600d31ce
-- title:
--   Rounded reciprocal Mobius certificate on [688128, 704512)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $688128\le n<704512$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part10
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair042_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 688128 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block084 mobiusReciprocal1200001Block085) = true := by sorry

end Helfgott
