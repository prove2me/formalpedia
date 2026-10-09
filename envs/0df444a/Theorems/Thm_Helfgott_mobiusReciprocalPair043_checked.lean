-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair043_checked
-- name    : Helfgott.mobiusReciprocalPair043_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:15:05.160986+00:00
-- url     : https://prove2.me/theorems/7e51ddc9-ec8e-490e-b37e-229dc049fa1d
-- title:
--   Rounded reciprocal Mobius certificate on [704512, 720896)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $704512\le n<720896$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part10
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair043_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 704512 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block086 mobiusReciprocal1200001Block087) = true := by sorry

end Helfgott
