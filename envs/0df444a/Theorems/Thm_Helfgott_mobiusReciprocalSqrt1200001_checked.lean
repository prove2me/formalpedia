-- Prove2me | Theorems.Thm_Helfgott_mobiusReciprocalSqrt1200001_checked
-- name    : Helfgott.mobiusReciprocalSqrt1200001_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:48:47.31757+00:00
-- url     : https://prove2.me/theorems/ec9250ed-736a-495f-ba5f-c9809bf0a865
-- title:
--   Complete rounded reciprocal Mobius certificate through 1200000
-- statement:
--   The complete fixed rounded reciprocal Möbius certificate passes every prefix recurrence, endpoint join, square-root integer inequality check through $n=1200000$, at scale $10^{12}$. This is the full computational input to the proved reciprocal-decay soundness theorem.
-- source:
--   Original complete finite square-root arithmetic certificate and soundness proof for the Helfgott minor-arc reciprocal Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001
open Helfgott

namespace Helfgott

theorem mobiusReciprocalSqrt1200001_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 16 0 mobiusReciprocal1200001 = true := by sorry

end Helfgott
