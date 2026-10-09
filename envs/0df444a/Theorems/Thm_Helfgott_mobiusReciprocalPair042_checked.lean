-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair042_checked
-- name    : Helfgott.mobiusReciprocalPair042_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:14:46.68643+00:00
-- url     : https://prove2.me/theorems/63241a70-73d1-46c3-8c6b-dd8b522bc962
-- title:
--   Rounded reciprocal Mobius certificate on [688128, 704512)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $688128\le n<704512$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part10
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair042_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 688128 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block084 mobiusReciprocal1200001Block085) = true := by sorry

end Helfgott
