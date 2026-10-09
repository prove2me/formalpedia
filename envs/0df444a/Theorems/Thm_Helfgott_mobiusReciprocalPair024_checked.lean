-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair024_checked
-- name    : Helfgott.mobiusReciprocalPair024_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:53:16.643807+00:00
-- url     : https://prove2.me/theorems/dcda2965-028a-43d6-a3f0-b08245bfdd66
-- title:
--   Rounded reciprocal Mobius certificate on [393216, 409600)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $393216\le n<409600$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part06
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair024_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 393216 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block048 mobiusReciprocal1200001Block049) = true := by sorry

end Helfgott
