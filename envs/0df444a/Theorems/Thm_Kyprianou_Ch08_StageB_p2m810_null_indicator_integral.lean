-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_null_indicator_integral
-- name    : Kyprianou.Ch08.StageB.p2m810_null_indicator_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:44:11.932816+00:00
-- url     : https://prove2.me/theorems/b4596c50-d745-4d95-a2f8-c9d81fd00904
-- title:
--   Null-measurable indicator integral equals the restricted integral
-- statement:
--   Replace the null-measurable set by an almost-everywhere equal measurable envelope, then use indicator measurability, integral congruence and restriction congruence.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); actual height law of Theorem 8.2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Null-measurable indicator integral equals the restricted integral -/
theorem p2m810_null_indicator_integral :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (g : Ω → ℝ) (A : Set Ω), Integrable g P → NullMeasurableSet A P →
      AEStronglyMeasurable (A.indicator g) P ∧
      (∫ ω, A.indicator g ω ∂P) = ∫ ω in A, g ω ∂P := by
  sorry
end Kyprianou.Ch08.StageB
