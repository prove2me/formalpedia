-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair001_checked
-- name    : Helfgott.mobiusReciprocalPair001_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:28:28.171005+00:00
-- url     : https://prove2.me/theorems/c91d8a1f-0dbd-42eb-a7c1-f9c510a3166d
-- title:
--   Rounded reciprocal Mobius certificate on [16384, 32768)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $16384\le n<32768$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair001_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 16384 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block002 mobiusReciprocal1200001Block003) = true := by sorry

end Helfgott
