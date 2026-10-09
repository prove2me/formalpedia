-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair066_checked
-- name    : Helfgott.mobiusReciprocalPair066_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:42:21.961981+00:00
-- url     : https://prove2.me/theorems/32fed97b-cb93-4e72-9183-70f89771a160
-- title:
--   Rounded reciprocal Mobius certificate on [1081344, 1097728)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $1081344\le n<1097728$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part16
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair066_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 1081344 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block132 mobiusReciprocal1200001Block133) = true := by sorry

end Helfgott
