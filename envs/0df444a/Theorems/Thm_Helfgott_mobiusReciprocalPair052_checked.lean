-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair052_checked
-- name    : Helfgott.mobiusReciprocalPair052_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:26:44.121646+00:00
-- url     : https://prove2.me/theorems/3d660992-4dcc-4f18-8da6-7a654a2f5c37
-- title:
--   Rounded reciprocal Mobius certificate on [851968, 868352)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $851968\le n<868352$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part13
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair052_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 851968 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block104 mobiusReciprocal1200001Block105) = true := by sorry

end Helfgott
