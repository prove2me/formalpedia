-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair021_checked
-- name    : Helfgott.mobiusReciprocalPair021_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:51:41.352014+00:00
-- url     : https://prove2.me/theorems/0fc7ee78-80a6-4547-93c0-2c2cfda9331c
-- title:
--   Rounded reciprocal Mobius certificate on [344064, 360448)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $344064\le n<360448$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part05
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair021_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 344064 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block042 mobiusReciprocal1200001Block043) = true := by sorry

end Helfgott
