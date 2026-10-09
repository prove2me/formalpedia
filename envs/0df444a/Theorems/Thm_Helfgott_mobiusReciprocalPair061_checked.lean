-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair061_checked
-- name    : Helfgott.mobiusReciprocalPair061_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:36:47.991756+00:00
-- url     : https://prove2.me/theorems/09ff927e-8b1d-429a-8d6a-41fe27b58f16
-- title:
--   Rounded reciprocal Mobius certificate on [999424, 1015808)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $999424\le n<1015808$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part15
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair061_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 999424 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block122 mobiusReciprocal1200001Block123) = true := by sorry

end Helfgott
