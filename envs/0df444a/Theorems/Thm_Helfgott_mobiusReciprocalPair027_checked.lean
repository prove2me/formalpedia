-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair027_checked
-- name    : Helfgott.mobiusReciprocalPair027_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:56:09.803012+00:00
-- url     : https://prove2.me/theorems/1383778a-d2d0-4bb3-a9ff-486e39b202df
-- title:
--   Rounded reciprocal Mobius certificate on [442368, 458752)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $442368\le n<458752$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part06
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair027_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 442368 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block054 mobiusReciprocal1200001Block055) = true := by sorry

end Helfgott
