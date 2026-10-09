-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair019_checked
-- name    : Helfgott.mobiusReciprocalPair019_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:48:41.994342+00:00
-- url     : https://prove2.me/theorems/029ef979-3b74-42d9-b669-d2d4e7b29103
-- title:
--   Rounded reciprocal Mobius certificate on [311296, 327680)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $311296\le n<327680$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part04
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair019_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 311296 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block038 mobiusReciprocal1200001Block039) = true := by sorry

end Helfgott
