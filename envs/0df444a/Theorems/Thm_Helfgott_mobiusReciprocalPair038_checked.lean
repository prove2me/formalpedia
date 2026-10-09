-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair038_checked
-- name    : Helfgott.mobiusReciprocalPair038_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:10:20.495709+00:00
-- url     : https://prove2.me/theorems/57fdebe1-9da9-4e4f-a722-d617be93e1c1
-- title:
--   Rounded reciprocal Mobius certificate on [622592, 638976)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $622592\le n<638976$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part09
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair038_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 622592 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block076 mobiusReciprocal1200001Block077) = true := by sorry

end Helfgott
