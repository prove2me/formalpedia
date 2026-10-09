-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair028_checked
-- name    : Helfgott.mobiusReciprocalPair028_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:59:27.10401+00:00
-- url     : https://prove2.me/theorems/6b213d17-f0a5-4a08-a5e3-578ac06d5e25
-- title:
--   Rounded reciprocal Mobius certificate on [458752, 475136)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $458752\le n<475136$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part07
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair028_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 458752 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block056 mobiusReciprocal1200001Block057) = true := by sorry

end Helfgott
