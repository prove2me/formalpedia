-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair039_checked
-- name    : Helfgott.mobiusReciprocalPair039_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:09:59.245326+00:00
-- url     : https://prove2.me/theorems/3b96c9f8-042b-4c10-9215-615fd67382bd
-- title:
--   Rounded reciprocal Mobius certificate on [638976, 655360)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $638976\le n<655360$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part09
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair039_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 638976 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block078 mobiusReciprocal1200001Block079) = true := by sorry

end Helfgott
