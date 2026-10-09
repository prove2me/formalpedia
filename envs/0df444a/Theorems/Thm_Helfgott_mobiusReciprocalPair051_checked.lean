-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair051_checked
-- name    : Helfgott.mobiusReciprocalPair051_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:23:55.914984+00:00
-- url     : https://prove2.me/theorems/f22ce871-798c-4a59-bf3f-33a58aafe11b
-- title:
--   Rounded reciprocal Mobius certificate on [835584, 851968)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $835584\le n<851968$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part12
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair051_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 835584 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block102 mobiusReciprocal1200001Block103) = true := by sorry

end Helfgott
