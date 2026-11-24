-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_record_discount_integrable
-- name    : Kyprianou.Ch08.StageB.p2m810_record_discount_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:44:00.13032+00:00
-- url     : https://prove2.me/theorems/1ad6307a-72e8-43d7-ad45-7570a1138ab3
-- title:
--   Discounted upper passage is integrable including infinite clocks
-- statement:
--   Use the proved strict upper passage clock measurability and the bounded measurable discountedAt function.
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
/-- Discounted upper passage is integrable including infinite clocks -/
theorem p2m810_record_discount_integrable :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q l : ℝ), 0 ≤ q → Integrable (fun ω => discountedAt q (tauPlus D.X l ω)) P := by
  sorry
end Kyprianou.Ch08.StageB
