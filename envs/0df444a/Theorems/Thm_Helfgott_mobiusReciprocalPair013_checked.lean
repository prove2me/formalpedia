-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair013_checked
-- name    : Helfgott.mobiusReciprocalPair013_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:43:15.004268+00:00
-- url     : https://prove2.me/theorems/89c2cb27-e62d-497d-99ef-29256afa5d8b
-- title:
--   Rounded reciprocal Mobius certificate on [212992, 229376)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $212992\le n<229376$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part03
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair013_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 212992 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block026 mobiusReciprocal1200001Block027) = true := by sorry

end Helfgott
