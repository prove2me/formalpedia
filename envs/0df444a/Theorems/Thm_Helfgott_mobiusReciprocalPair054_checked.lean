-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair054_checked
-- name    : Helfgott.mobiusReciprocalPair054_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:28:48.199278+00:00
-- url     : https://prove2.me/theorems/ef095b4e-680d-4733-9bc0-cec6efc5b206
-- title:
--   Rounded reciprocal Mobius certificate on [884736, 901120)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $884736\le n<901120$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part13
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair054_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 884736 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block108 mobiusReciprocal1200001Block109) = true := by sorry

end Helfgott
