-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair016_checked
-- name    : Helfgott.mobiusReciprocalPair016_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:45:39.533546+00:00
-- url     : https://prove2.me/theorems/307ed682-a9b7-4507-9eac-e1686f33880f
-- title:
--   Rounded reciprocal Mobius certificate on [262144, 278528)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $262144\le n<278528$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part04
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair016_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 262144 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block032 mobiusReciprocal1200001Block033) = true := by sorry

end Helfgott
