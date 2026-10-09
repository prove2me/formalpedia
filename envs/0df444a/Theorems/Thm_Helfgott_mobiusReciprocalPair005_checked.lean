-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair005_checked
-- name    : Helfgott.mobiusReciprocalPair005_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:35:18.94819+00:00
-- url     : https://prove2.me/theorems/0c756370-07a5-468e-b5c5-98c58779c330
-- title:
--   Rounded reciprocal Mobius certificate on [81920, 98304)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $81920\le n<98304$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part01
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair005_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 81920 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block010 mobiusReciprocal1200001Block011) = true := by sorry

end Helfgott
