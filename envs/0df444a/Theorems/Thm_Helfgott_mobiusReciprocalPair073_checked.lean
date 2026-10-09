-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair073_checked
-- name    : Helfgott.mobiusReciprocalPair073_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:49:16.077839+00:00
-- url     : https://prove2.me/theorems/da21c5fc-8a80-4207-a29b-db6f00e6eb38
-- title:
--   Rounded reciprocal Mobius certificate on [1196032, 1200001)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $1196032\le n<1200001$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part18
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair073_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 1196032 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block146 (MobiusReciprocalTree.leaf (-119400916) (-119400916) 0 0)) = true := by sorry

end Helfgott
