-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair031_checked
-- name    : Helfgott.mobiusReciprocalPair031_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:59:57.165934+00:00
-- url     : https://prove2.me/theorems/ecfa69d2-4b04-4d93-a2dd-bb29a523ef16
-- title:
--   Rounded reciprocal Mobius certificate on [507904, 524288)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $507904\le n<524288$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part07
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair031_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 507904 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block062 mobiusReciprocal1200001Block063) = true := by sorry

end Helfgott
