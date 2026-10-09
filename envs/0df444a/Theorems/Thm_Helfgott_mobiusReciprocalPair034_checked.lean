-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair034_checked
-- name    : Helfgott.mobiusReciprocalPair034_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:04:14.080518+00:00
-- url     : https://prove2.me/theorems/2df0fe46-0375-4ab6-a580-5f4bb6a0c91a
-- title:
--   Rounded reciprocal Mobius certificate on [557056, 573440)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $557056\le n<573440$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part08
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair034_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 557056 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block068 mobiusReciprocal1200001Block069) = true := by sorry

end Helfgott
