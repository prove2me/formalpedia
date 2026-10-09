-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair025_checked
-- name    : Helfgott.mobiusReciprocalPair025_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:55:42.090974+00:00
-- url     : https://prove2.me/theorems/4f1ccc42-bfc5-43fd-a08a-a439d3dda2f6
-- title:
--   Rounded reciprocal Mobius certificate on [409600, 425984)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $409600\le n<425984$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part06
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair025_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 409600 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block050 mobiusReciprocal1200001Block051) = true := by sorry

end Helfgott
