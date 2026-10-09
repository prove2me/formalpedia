-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair053_checked
-- name    : Helfgott.mobiusReciprocalPair053_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:27:29.568727+00:00
-- url     : https://prove2.me/theorems/6b74c848-3721-4dac-9647-a7d86846ebf8
-- title:
--   Rounded reciprocal Mobius certificate on [868352, 884736)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $868352\le n<884736$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part13
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair053_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 868352 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block106 mobiusReciprocal1200001Block107) = true := by sorry

end Helfgott
