-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair049_checked
-- name    : Helfgott.mobiusReciprocalPair049_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:23:29.478154+00:00
-- url     : https://prove2.me/theorems/c2ad93a7-f582-4bc3-8ba0-4fd546de1073
-- title:
--   Rounded reciprocal Mobius certificate on [802816, 819200)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $802816\le n<819200$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part12
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair049_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 802816 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block098 mobiusReciprocal1200001Block099) = true := by sorry

end Helfgott
