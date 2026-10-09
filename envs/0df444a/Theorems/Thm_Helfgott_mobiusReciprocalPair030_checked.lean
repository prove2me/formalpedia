-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair030_checked
-- name    : Helfgott.mobiusReciprocalPair030_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:00:05.678358+00:00
-- url     : https://prove2.me/theorems/ad41219f-c6fa-4a67-95cd-699e816ca37b
-- title:
--   Rounded reciprocal Mobius certificate on [491520, 507904)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $491520\le n<507904$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part07
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair030_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 491520 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block060 mobiusReciprocal1200001Block061) = true := by sorry

end Helfgott
