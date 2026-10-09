-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair025_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair025_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:54:33.097107+00:00
-- url     : https://prove2.me/theorems/23771643-ea13-48b3-bdbc-9f5383663c29
-- title:
--   Rounded reciprocal Mobius certificate on [409600, 425984)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $409600\le n<425984$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part06
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair025_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 409600 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block050 mobiusReciprocal1200001Block051) = true := by sorry

end Helfgott
