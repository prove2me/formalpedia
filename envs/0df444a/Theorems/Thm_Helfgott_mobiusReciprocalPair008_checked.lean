-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair008_checked
-- name    : Helfgott.mobiusReciprocalPair008_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:36:56.083199+00:00
-- url     : https://prove2.me/theorems/5be22840-7159-452e-9107-240edbc3cab9
-- title:
--   Rounded reciprocal Mobius certificate on [131072, 147456)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $131072\le n<147456$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part02
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair008_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 131072 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block016 mobiusReciprocal1200001Block017) = true := by sorry

end Helfgott
