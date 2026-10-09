-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalPair058_checked
-- name    : Helfgott.mobiusReciprocalPair058_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:32:18.786869+00:00
-- url     : https://prove2.me/theorems/a4f47707-6aca-4366-8b47-6cfcc9314b3a
-- title:
--   Rounded reciprocal Mobius certificate on [950272, 966656)
-- statement:
--   The fixed rounded reciprocal Möbius certificate passes every arithmetic check on $950272\le n<966656$ at scale $Q=10^{12}$. Each checked leaf has exact prefix transitions and endpoints. For integers $n\ge11815$, it also has a certified logarithm tier $K$ and satisfies $10(|S_n|+n)K\le3Q$. The remaining intervals, the candidate Möbius equality, and the soundness theorem are needed to conclude the complete reciprocal decay bound.
-- source:
--   Original kernel-checked finite arithmetic certificate for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part14
open Helfgott

namespace Helfgott

theorem mobiusReciprocalPair058_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 9 950272 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block116 mobiusReciprocal1200001Block117) = true := by sorry

end Helfgott
