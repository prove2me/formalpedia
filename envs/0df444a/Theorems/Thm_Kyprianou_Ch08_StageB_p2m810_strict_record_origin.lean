-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_strict_record_origin
-- name    : Kyprianou.Ch08.StageB.p2m810_strict_record_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:08:12.546797+00:00
-- url     : https://prove2.me/theorems/dcf17e13-3128-4e95-823a-c567167b47ac
-- title:
--   Strict drawdown record survival from initial maximum zero
-- statement:
--   Use the actual excursion height law at a+1/(k+1), the decreasing-event integral limit, and continuity from below of excursion measure on the increasing sets [a+1/(k+1),infinity). The right derivative formula identifies the strict height rate.
-- source:
--   Kyprianou (2006), Theorems 8.2 and 8.10(i).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Strict drawdown record survival from initial maximum zero -/
theorem p2m810_strict_record_origin :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q a l : ℝ), 0 ≤ q → 0 < a → 0 < l →
      (∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X 0 a ω
        then discountedAt q (tauPlus D.X l ω) else 0 ∂P) =
      Real.exp (-(derivWithin (W q) (Ici a) a / W q a) * l) := by
  sorry
end Kyprianou.Ch08.StageB
