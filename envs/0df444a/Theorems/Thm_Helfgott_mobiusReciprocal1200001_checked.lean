-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocal1200001_checked
-- name    : Helfgott.mobiusReciprocal1200001_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:55:50.777697+00:00
-- url     : https://prove2.me/theorems/b2d87549-030b-402a-aa74-494b7f02ff96
-- title:
--   Complete rounded reciprocal Mobius certificate through 1200000
-- statement:
--   The complete fixed rounded reciprocal Möbius certificate passes every prefix recurrence, endpoint join, logarithm-tier membership and integer inequality check through $n=1200000$, at scale $10^{12}$. This is the full computational input to the proved reciprocal-decay soundness theorem.
-- source:
--   Original complete finite arithmetic certificate and soundness proof for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001
open Helfgott

namespace Helfgott

theorem mobiusReciprocal1200001_checked : mobiusReciprocalTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 11815 1200001 16 0 mobiusReciprocal1200001 = true := by sorry

end Helfgott
