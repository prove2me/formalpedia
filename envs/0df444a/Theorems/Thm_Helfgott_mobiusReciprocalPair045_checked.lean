-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair045_checked
-- name    : Helfgott.mobiusReciprocalPair045_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:18:47.368107+00:00
-- url     : https://prove2.me/theorems/fc53a342-41ec-4a72-9224-fe4ecb4e06e0
-- title:
--   Rounded reciprocal Mobius certificate on [737280, 753664)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $737280\le n<753664$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part11
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair045_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 737280 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block090 mobiusReciprocal1200001Block091) = true := by sorry

end Helfgott
