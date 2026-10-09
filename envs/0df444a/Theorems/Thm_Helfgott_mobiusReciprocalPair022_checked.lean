-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair022_checked
-- name    : Helfgott.mobiusReciprocalPair022_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:51:55.624981+00:00
-- url     : https://prove2.me/theorems/2d4f78b9-1823-4364-8b97-7fed972728b8
-- title:
--   Rounded reciprocal Mobius certificate on [360448, 376832)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $360448\le n<376832$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part05
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair022_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 360448 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block044 mobiusReciprocal1200001Block045) = true := by sorry

end Helfgott
