-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_reset_quotient_algebra
-- name    : Kyprianou.Ch08.StageB.p2m810_reset_quotient_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:26:19.392548+00:00
-- url     : https://prove2.me/theorems/041a038e-1115-458f-9bad-9a6a53b2e0e1
-- title:
--   Algebraic renewal quotient cancellation
-- statement:
--   Pure real algebra, with positive scale values and a renewal factor strictly below one.
-- source:
--   Kyprianou (2006), Theorem 8.10(ii), and Theorem 8.1.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Algebraic renewal quotient cancellation -/
theorem p2m810_reset_quotient_algebra :
    ∀ (wx w0 wb zx z0 zb : ℝ),
      0 < w0 → 0 < wb → z0 - zb * w0 / wb < 1 →
      wx / wb + (zx - zb * wx / wb) *
        ((w0 / wb) / (1 - (z0 - zb * w0 / wb))) =
        (zx - wx * ((z0 - 1) / w0)) /
          (zb - wb * ((z0 - 1) / w0)) := by
  sorry
end Kyprianou.Ch08.StageB
