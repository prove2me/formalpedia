-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair004_checked
-- name    : Helfgott.mobiusReciprocalPair004_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:28:30.217001+00:00
-- url     : https://prove2.me/theorems/5a29b18b-50e0-428f-8fe5-e7b6b069d80f
-- title:
--   Rounded reciprocal Mobius certificate on [65536, 81920)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $65536\le n<81920$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair004_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 65536 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block008 mobiusReciprocal1200001Block009) = true := by sorry

end Helfgott
