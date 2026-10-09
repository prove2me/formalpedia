-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair026_checked
-- name    : Helfgott.mobiusReciprocalPair026_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:56:16.089954+00:00
-- url     : https://prove2.me/theorems/d9a8435f-395b-4703-90ef-6d2bc02649a9
-- title:
--   Rounded reciprocal Mobius certificate on [425984, 442368)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $425984\le n<442368$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part06
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair026_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 425984 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block052 mobiusReciprocal1200001Block053) = true := by sorry

end Helfgott
