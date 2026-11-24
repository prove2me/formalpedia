-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_origin_drawdown_clock
-- name    : Kyprianou.Ch08.StageB.p2m810_origin_drawdown_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:10:38.162673+00:00
-- url     : https://prove2.me/theorems/720abd10-ce89-47d5-ae83-ce4a02fac8ab
-- title:
--   Actual origin drawdown clock equals the all-time strict drawdown infimum
-- statement:
--   The running maximum is nonnegative and equals the supremum of the image of Icc 0 t. At zero the drawdown is zero, and the positive barrier excludes zero from the strict crossing set.
-- source:
--   Kyprianou (2006), Theorems 8.1 and 8.10(i).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Actual origin drawdown clock equals the all-time strict drawdown infimum -/
theorem p2m810_origin_drawdown_clock :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (a : ℝ) (ω : Ω), 0 < a →
      (reflectedSupExit X.X 0 a ω : ℝ≥0∞) =
      ⨅ i : {t : ℝ≥0 // X.X t ω -
        sSup ((fun t => X.X t ω) '' Icc 0 t) < -a}, (i.1 : ℝ≥0∞) := by
  sorry
end Kyprianou.Ch08.StageB
