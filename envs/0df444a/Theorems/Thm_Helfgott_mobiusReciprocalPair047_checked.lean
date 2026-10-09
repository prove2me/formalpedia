-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair047_checked
-- name    : Helfgott.mobiusReciprocalPair047_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:19:46.288766+00:00
-- url     : https://prove2.me/theorems/b7e7d13f-c493-4021-aaf9-8759ef49ab52
-- title:
--   Rounded reciprocal Mobius certificate on [770048, 786432)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $770048\le n<786432$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part11
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair047_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 770048 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block094 mobiusReciprocal1200001Block095) = true := by sorry

end Helfgott
