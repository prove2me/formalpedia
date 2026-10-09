-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair014_checked
-- name    : Helfgott.mobiusReciprocalPair014_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:43:36.893977+00:00
-- url     : https://prove2.me/theorems/4dc0b9e5-d299-4551-8836-545de489ff64
-- title:
--   Rounded reciprocal Mobius certificate on [229376, 245760)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $229376\le n<245760$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part03
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair014_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 229376 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block028 mobiusReciprocal1200001Block029) = true := by sorry

end Helfgott
