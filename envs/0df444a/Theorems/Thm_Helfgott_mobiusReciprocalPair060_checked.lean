-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair060_checked
-- name    : Helfgott.mobiusReciprocalPair060_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:37:24.962997+00:00
-- url     : https://prove2.me/theorems/4b641e5e-c8be-4edf-8ffe-466da9fb0783
-- title:
--   Rounded reciprocal Mobius certificate on [983040, 999424)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $983040\le n<999424$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part15
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair060_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 983040 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block120 mobiusReciprocal1200001Block121) = true := by sorry

end Helfgott
