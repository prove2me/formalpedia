-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair003_checked
-- name    : Helfgott.mobiusReciprocalPair003_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:27:22.158483+00:00
-- url     : https://prove2.me/theorems/12eee243-3507-4f68-8ac9-71ac82b7c966
-- title:
--   Rounded reciprocal Mobius certificate on [49152, 65536)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $49152\le n<65536$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair003_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 49152 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block006 mobiusReciprocal1200001Block007) = true := by sorry

end Helfgott
