-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41PredictableZeroSetV6
-- name    : Kyprianou.Ch04.exercise41PredictableZeroSetV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:22:30.840704+00:00
-- url     : https://prove2.me/theorems/b35e1164-a5fe-58fc-b6cc-aebe5d9f3bb1
-- title:
--   The positive-time prezero set is predictable and product measurable
-- statement:
--   The positive-time prezero set is predictable and product measurable
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41PredictableZeroSetV6
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (T : NNReal) :
    let E : Set (NNReal × Ω) := {p | 0 < p.1 ∧ p.1 ≤ T ∧
      Function.leftLim (fun t => L.X t p.2) p.1 = 0}
    MeasurableSet[F.rightCont.predictable] E ∧ MeasurableSet E  := by
  sorry
