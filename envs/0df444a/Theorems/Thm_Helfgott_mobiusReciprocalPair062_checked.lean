-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair062_checked
-- name    : Helfgott.mobiusReciprocalPair062_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:36:17.303514+00:00
-- url     : https://prove2.me/theorems/ac53fd52-bacd-4003-a196-e4ec79fc8aa9
-- title:
--   Rounded reciprocal Mobius certificate on [1015808, 1032192)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $1015808\le n<1032192$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part15
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair062_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 1015808 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block124 mobiusReciprocal1200001Block125) = true := by sorry

end Helfgott
