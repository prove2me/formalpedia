-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair035_checked
-- name    : Helfgott.mobiusReciprocalPair035_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:05:05.966684+00:00
-- url     : https://prove2.me/theorems/1a5eb698-5396-4994-8481-35e74afc1621
-- title:
--   Rounded reciprocal Mobius certificate on [573440, 589824)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $573440\le n<589824$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part08
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair035_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 573440 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block070 mobiusReciprocal1200001Block071) = true := by sorry

end Helfgott
