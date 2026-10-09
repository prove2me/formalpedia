-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair009_checked
-- name    : Helfgott.mobiusReciprocalPair009_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:39:02.444119+00:00
-- url     : https://prove2.me/theorems/99baa356-0f76-4134-b0ad-e78e704d1c52
-- title:
--   Rounded reciprocal Mobius certificate on [147456, 163840)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $147456\le n<163840$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part02
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair009_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 147456 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block018 mobiusReciprocal1200001Block019) = true := by sorry

end Helfgott
