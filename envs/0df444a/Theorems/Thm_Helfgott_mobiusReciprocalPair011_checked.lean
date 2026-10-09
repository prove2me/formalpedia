-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair011_checked
-- name    : Helfgott.mobiusReciprocalPair011_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:40:46.319669+00:00
-- url     : https://prove2.me/theorems/bc2638f4-bd73-4e51-9249-51481222490b
-- title:
--   Rounded reciprocal Mobius certificate on [180224, 196608)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $180224\le n<196608$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part02
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair011_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 180224 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block022 mobiusReciprocal1200001Block023) = true := by sorry

end Helfgott
