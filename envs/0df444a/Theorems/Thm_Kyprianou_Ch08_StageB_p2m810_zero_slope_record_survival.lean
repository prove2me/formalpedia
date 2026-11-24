-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_zero_slope_record_survival
-- name    : Kyprianou.Ch08.StageB.p2m810_zero_slope_record_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:21:33.993958+00:00
-- url     : https://prove2.me/theorems/12771f63-9bd7-4c4e-8259-021dfd315533
-- title:
--   Zero right slope implies certain record survival from the maximum
-- statement:
--   Theorem 8.2 forces Phi(q)=0 and the strict excursion tail to vanish. Consequently q=0 and every finite positive upper record is reached before the strict drawdown almost surely; equivalently its discounted payoff is one.
-- source:
--   Kyprianou (2006), Theorem 8.10(i), record renewal; Theorem 8.2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Zero right slope implies certain record survival from the maximum -/
theorem p2m810_zero_slope_record_survival :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      derivWithin (W q) (Ici a) a = 0 →
      q = 0 ∧ ∀ l : ℝ, x < l →
        (∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X 0 a ω
          then discountedAt q (tauPlus D.X l ω) else 0 ∂P) = 1 := by
  sorry
end Kyprianou.Ch08.StageB
