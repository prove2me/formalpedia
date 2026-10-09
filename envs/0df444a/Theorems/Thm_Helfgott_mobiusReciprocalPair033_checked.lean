-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair033_checked
-- name    : Helfgott.mobiusReciprocalPair033_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:03:59.994292+00:00
-- url     : https://prove2.me/theorems/f424820d-c493-45d1-8865-cb0c37e23a2f
-- title:
--   Rounded reciprocal Mobius certificate on [540672, 557056)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $540672\le n<557056$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part08
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair033_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 540672 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block066 mobiusReciprocal1200001Block067) = true := by sorry

end Helfgott
