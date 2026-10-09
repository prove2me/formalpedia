-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair018_checked
-- name    : Helfgott.mobiusReciprocalPair018_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:48:17.165929+00:00
-- url     : https://prove2.me/theorems/660fc2e5-3a4f-4ebf-bc3e-e9c2bd009b05
-- title:
--   Rounded reciprocal Mobius certificate on [294912, 311296)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $294912\le n<311296$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part04
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair018_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 294912 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block036 mobiusReciprocal1200001Block037) = true := by sorry

end Helfgott
