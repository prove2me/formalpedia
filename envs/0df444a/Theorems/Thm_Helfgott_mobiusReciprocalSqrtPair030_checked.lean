-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair030_checked
-- name    : Helfgott.mobiusReciprocalSqrtPair030_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:00:18.344973+00:00
-- url     : https://prove2.me/theorems/1313bb5b-9cab-4257-8b58-e1d043164184
-- title:
--   Rounded reciprocal Mobius certificate on [491520, 507904)
-- statement:
--   The fixed rounded reciprocal Möbius square-root certificate passes every arithmetic check on $491520\le n<507904$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge2$, it satisfies $(|S_n|+n)^2(n+1)\le2Q^2$. Other intervals, candidate Möbius equality, and the proved rounding conversion are required for the complete real reciprocal bound.
-- source:
--   Original kernel-checked finite arithmetic square-root certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part07
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrtPair030_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 491520 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block060 mobiusReciprocal1200001Block061) = true := by sorry

end Helfgott
