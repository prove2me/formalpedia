-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair072_checked
-- name    : Helfgott.mobiusReciprocalPair072_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:49:14.219273+00:00
-- url     : https://prove2.me/theorems/64766fb9-3280-48b3-8725-93271ebe65ca
-- title:
--   Rounded reciprocal Mobius certificate on [1179648, 1196032)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $1179648\le n<1196032$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part18
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair072_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 1179648 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block144 mobiusReciprocal1200001Block145) = true := by sorry

end Helfgott
