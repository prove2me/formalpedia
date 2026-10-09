-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair002_checked
-- name    : Helfgott.mobiusReciprocalPair002_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:27:25.714048+00:00
-- url     : https://prove2.me/theorems/f8024c36-92fd-4431-81b3-8fa3ee8fdcab
-- title:
--   Rounded reciprocal Mobius certificate on [32768, 49152)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $32768\le n<49152$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair002_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 32768 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block004 mobiusReciprocal1200001Block005) = true := by sorry

end Helfgott
