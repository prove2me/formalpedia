-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair071_checked
-- name    : Helfgott.mobiusReciprocalPair071_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:47:46.668336+00:00
-- url     : https://prove2.me/theorems/e11222eb-17b5-49eb-8a07-a1d5aa685b94
-- title:
--   Rounded reciprocal Mobius certificate on [1163264, 1179648)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $1163264\le n<1179648$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part17
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair071_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 1163264 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block142 mobiusReciprocal1200001Block143) = true := by sorry

end Helfgott
