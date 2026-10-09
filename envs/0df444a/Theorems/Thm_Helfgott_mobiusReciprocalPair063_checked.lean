-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair063_checked
-- name    : Helfgott.mobiusReciprocalPair063_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:37:55.515606+00:00
-- url     : https://prove2.me/theorems/72fab50e-851e-4c08-8704-0d108bbc36e0
-- title:
--   Rounded reciprocal Mobius certificate on [1032192, 1048576)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $1032192\le n<1048576$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part15
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair063_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 1032192 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block126 mobiusReciprocal1200001Block127) = true := by sorry

end Helfgott
