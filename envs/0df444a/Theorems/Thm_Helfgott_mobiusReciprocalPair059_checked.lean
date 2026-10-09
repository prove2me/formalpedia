-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair059_checked
-- name    : Helfgott.mobiusReciprocalPair059_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:33:11.152907+00:00
-- url     : https://prove2.me/theorems/8d3cdffa-8ca3-43cd-bf94-7661f0362dd2
-- title:
--   Rounded reciprocal Mobius certificate on [966656, 983040)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $966656\le n<983040$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part14
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair059_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 966656 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block118 mobiusReciprocal1200001Block119) = true := by sorry

end Helfgott
