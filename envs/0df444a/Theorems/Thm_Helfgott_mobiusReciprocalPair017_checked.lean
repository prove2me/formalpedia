-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair017_checked
-- name    : Helfgott.mobiusReciprocalPair017_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:47:42.270983+00:00
-- url     : https://prove2.me/theorems/fcb8821e-fa39-44ec-9808-1c942e59b63c
-- title:
--   Rounded reciprocal Mobius certificate on [278528, 294912)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $278528\le n<294912$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part04
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair017_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 278528 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block034 mobiusReciprocal1200001Block035) = true := by sorry

end Helfgott
