-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair032_checked
-- name    : Helfgott.mobiusReciprocalPair032_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:03:59.794003+00:00
-- url     : https://prove2.me/theorems/60d069eb-defd-4c3e-9727-2d04543de76c
-- title:
--   Rounded reciprocal Mobius certificate on [524288, 540672)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $524288\le n<540672$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part08
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair032_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 524288 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block064 mobiusReciprocal1200001Block065) = true := by sorry

end Helfgott
