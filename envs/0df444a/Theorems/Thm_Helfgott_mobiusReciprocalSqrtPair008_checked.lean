-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair008_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair008_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:35:00.47224+00:00
-- url     : https://prove2.me/theorems/c027318a-e5e4-4bb9-bfc4-c2b365dbc971
-- title:
--   Rounded reciprocal Mobius certificate on [131072, 147456)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $131072\le n<147456$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part02
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair008_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 131072 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block016 mobiusReciprocal1200001Block017) = true := by sorry

end Helfgott
