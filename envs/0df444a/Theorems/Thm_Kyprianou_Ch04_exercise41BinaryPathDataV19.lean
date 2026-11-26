-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41BinaryPathDataV19
-- name    : Kyprianou.Ch04.exercise41BinaryPathDataV19
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:20:04.712187+00:00
-- url     : https://prove2.me/theorems/175761e8-b572-5115-851f-dd7269a202ba
-- title:
--   Indicator path and its canonical left limits
-- statement:
--   Indicator path and its canonical left limits
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41BinaryPathDataV19
    (x l : NNReal → ℝ)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → Tendsto x (nhdsWithin s (Iio s)) (nhds (l s)))
    (hNoJump : ∀ s, 0 < s → Function.leftLim x s = 0 → x s = 0)
    (hDep : ∀ s, x s = 0 → ∃ e : NNReal, 0 < e ∧
      ∀ u : NNReal, 0 < u → u < e → 0 < x (s+u))
    (hArr : ∀ s, 0 < s → x s = 0 → Function.leftLim x s = 0 →
      ∃ e : NNReal, 0 < e ∧ ∀ u : NNReal, 0 < u →
        u < min e s → x (s-u) < 0) :
    let f := fun u => if x u < 0 then (-1 : ℝ) else 0
    (∀ s, ContinuousWithinAt f (Ici s) s) ∧
    (∀ s, 0 < s → Tendsto f (nhdsWithin s (Iio s)) (nhds (Function.leftLim f s))) ∧
    (∀ s, 0 < s → Function.leftLim f s = (if 0 < l s then 0 else -1)) := by
  sorry
