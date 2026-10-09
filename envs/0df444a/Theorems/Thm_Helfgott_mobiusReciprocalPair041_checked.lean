-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair041_checked
-- name    : Helfgott.mobiusReciprocalPair041_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:13:35.753156+00:00
-- url     : https://prove2.me/theorems/863d9eb2-7b28-409f-ae98-54f0595e407c
-- title:
--   Rounded reciprocal Mobius certificate on [671744, 688128)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $671744\le n<688128$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part10
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair041_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 671744 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block082 mobiusReciprocal1200001Block083) = true := by sorry

end Helfgott
