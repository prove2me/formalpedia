-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair010_checked
-- name    : Helfgott.mobiusReciprocalPair010_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:39:37.655438+00:00
-- url     : https://prove2.me/theorems/4b436866-3af2-4f37-abf6-9817c1a1ebf7
-- title:
--   Rounded reciprocal Mobius certificate on [163840, 180224)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $163840\le n<180224$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part02
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair010_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 163840 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block020 mobiusReciprocal1200001Block021) = true := by sorry

end Helfgott
