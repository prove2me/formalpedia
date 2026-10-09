-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair046_checked
-- name    : Helfgott.mobiusReciprocalPair046_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:19:12.293496+00:00
-- url     : https://prove2.me/theorems/bbc5ac16-4115-4211-b73c-24bdb19bc454
-- title:
--   Rounded reciprocal Mobius certificate on [753664, 770048)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $753664\le n<770048$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part11
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair046_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 753664 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block092 mobiusReciprocal1200001Block093) = true := by sorry

end Helfgott
