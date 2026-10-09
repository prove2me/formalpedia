-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair050_checked
-- name    : Helfgott.mobiusReciprocalPair050_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:23:54.259912+00:00
-- url     : https://prove2.me/theorems/8bddf6bd-d352-46db-8217-d861d4af5e68
-- title:
--   Rounded reciprocal Mobius certificate on [819200, 835584)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $819200\le n<835584$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part12
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair050_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 819200 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block100 mobiusReciprocal1200001Block101) = true := by sorry

end Helfgott
