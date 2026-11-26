-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41FutureFunctionalLawV24
-- name    : Kyprianou.Ch04.exercise41FutureFunctionalLawV24
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T15:08:00.170485+00:00
-- url     : https://prove2.me/theorems/b7736aea-1667-53e3-abce-2ff9cc5be0d8
-- title:
--   Product law for a measurable functional of the future path
-- statement:
--   Product law for a measurable functional of the future path
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41FutureFunctionalLawV24
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal inferInstance) (L : SpectrallyNegativeLevy P F)
    (s : NNReal) (G : (NNReal → ℝ) → ℝ) (hG : Measurable G) :
    Measure.map (fun w => (L.X s w, G (fun t => L.X (s+t) w - L.X s w))) P =
      (Measure.map (L.X s) P).prod (Measure.map (fun w => G (fun t => L.X t w)) P) := by
  sorry
