-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41PrezeroProductNullV6
-- name    : Kyprianou.Ch04.exercise41PrezeroProductNullV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:31:15.41954+00:00
-- url     : https://prove2.me/theorems/3853efe5-fcee-4c1d-a4f0-a5cac272b78c
-- title:
--   The positive-time prezero set has zero product occupation measure
-- statement:
--   The positive-time prezero set has zero product occupation measure
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41PrezeroProductNullV6
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) (T : NNReal) :
    let E : Set (NNReal × Ω) := {p | 0 < p.1 ∧ p.1 ≤ T ∧
      Function.leftLim (fun t => L.X t p.2) p.1 = 0}
    ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E = 0  := by
  sorry
