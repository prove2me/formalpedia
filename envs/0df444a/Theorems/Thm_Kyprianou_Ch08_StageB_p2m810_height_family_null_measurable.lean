-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_height_family_null_measurable
-- name    : Kyprianou.Ch08.StageB.p2m810_height_family_null_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:44:06.430163+00:00
-- url     : https://prove2.me/theorems/f787fa64-ff0f-4b82-bbd1-6ba4f94987c9
-- title:
--   Source strict pre-record height events are null-measurable
-- statement:
--   Transfer the given actual source model to the proved filtered Avram model and use the existing general-b strict height event theorem and its null-measurability transport.
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
/-- Source strict pre-record height events are null-measurable -/
theorem p2m810_height_family_null_measurable :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (l h : ℝ), 0 < l → 0 < h →
      NullMeasurableSet {ω | NoDrawdownBeforeUpcrossing D.X l h ω} P := by
  sorry
end Kyprianou.Ch08.StageB
