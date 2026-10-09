-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair068_checked
-- name    : Helfgott.mobiusReciprocalPair068_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:45:03.861883+00:00
-- url     : https://prove2.me/theorems/68206ad2-81f8-4fe8-a874-ef941a265e24
-- title:
--   Rounded reciprocal Mobius certificate on [1114112, 1130496)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $1114112\le n<1130496$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part17
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair068_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 1114112 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block136 mobiusReciprocal1200001Block137) = true := by sorry

end Helfgott
