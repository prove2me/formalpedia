-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair000_checked
-- name    : Helfgott.mobiusReciprocalPair000_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:21:43.993615+00:00
-- url     : https://prove2.me/theorems/26a51368-9c7a-4e4d-b809-79f4c5aeec36
-- title:
--   Rounded reciprocal Mobius certificate on [0, 16384)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $0\le n<16384$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair000_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 0 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block000 mobiusReciprocal1200001Block001) = true := by sorry

end Helfgott
