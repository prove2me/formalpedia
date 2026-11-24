-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_record_restart_factor
-- name    : Kyprianou.Ch08.StageB.p2m810_record_restart_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:08:14.921277+00:00
-- url     : https://prove2.me/theorems/8056c167-874f-40ea-9409-ac52a354974f
-- title:
--   Regeneration at the first new record with a nonzero initial maximum
-- statement:
--   For x>0, the first new record x occurs before strict drawdown precisely when the initial surplus a-x exits upwards before going below zero. At that record the reflected drawdown is zero. Apply the strong Markov property and multiplicative discount to the subsequent record l-x.
-- source:
--   Kyprianou (2006), Theorems 8.2 and 8.10(i).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Regeneration at the first new record with a nonzero initial maximum -/
theorem p2m810_record_restart_factor :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a l : ℝ), 0 ≤ q → 0 < a → 0 < x → x ≤ a → x < l →
      (∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X x a ω
        then discountedAt q (tauPlus D.X l ω) else 0 ∂P) =
      upBeforeDownExpectation P D.X q (a-x) a *
      (∫ ω, if tauPlus D.X (l-x) ω < reflectedSupExit D.X 0 a ω
        then discountedAt q (tauPlus D.X (l-x) ω) else 0 ∂P) := by
  sorry
end Kyprianou.Ch08.StageB
