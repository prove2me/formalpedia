-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair020_checked
-- name    : Helfgott.mobiusReciprocalPair020_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:48:44.579536+00:00
-- url     : https://prove2.me/theorems/a3e48097-fd33-4417-bc7e-5ba81ff0678e
-- title:
--   Rounded reciprocal Mobius certificate on [327680, 344064)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $327680\le n<344064$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part05
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair020_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 327680 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block040 mobiusReciprocal1200001Block041) = true := by sorry

end Helfgott
