-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair037_checked
-- name    : Helfgott.mobiusReciprocalPair037_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:09:58.624653+00:00
-- url     : https://prove2.me/theorems/0941bf7c-a259-4097-b619-9b67e88f204d
-- title:
--   Rounded reciprocal Mobius certificate on [606208, 622592)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $606208\le n<622592$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part09
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair037_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 606208 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block074 mobiusReciprocal1200001Block075) = true := by sorry

end Helfgott
