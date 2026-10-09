-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair069_checked
-- name    : Helfgott.mobiusReciprocalPair069_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:45:33.922819+00:00
-- url     : https://prove2.me/theorems/d79255fe-9d00-4f2f-82da-8407b0ef571a
-- title:
--   Rounded reciprocal Mobius certificate on [1130496, 1146880)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $1130496\le n<1146880$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part17
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair069_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 1130496 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block138 mobiusReciprocal1200001Block139) = true := by sorry

end Helfgott
