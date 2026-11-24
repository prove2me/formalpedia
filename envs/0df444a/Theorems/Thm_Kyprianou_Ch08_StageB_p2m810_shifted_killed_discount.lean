-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_shifted_killed_discount
-- name    : Kyprianou.Ch08.StageB.p2m810_shifted_killed_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:15:56.409285+00:00
-- url     : https://prove2.me/theorems/fce95262-a752-4dd5-b1b4-9fadc2487016
-- title:
--   Finite-shift killed discount factorisation
-- statement:
--   Addition of a finite first record preserves the strict order of the residual extended clocks. If the upper residual clock is first it is finite, and the exponential discount factors.
-- source:
--   Kyprianou (2006), Theorem 8.10(i).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Finite-shift killed discount factorisation -/
theorem p2m810_shifted_killed_discount :
    ∀ (q : ℝ) (u : ℝ≥0) (U R : ℝ≥0∞),
      (if (u : ℝ≥0∞)+U < (u : ℝ≥0∞)+R
        then discountedAt q ((u : ℝ≥0∞)+U) else 0) =
      Real.exp (-q*(u:ℝ)) * (if U < R then discountedAt q U else 0) := by
  sorry
end Kyprianou.Ch08.StageB
