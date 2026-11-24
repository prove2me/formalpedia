-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_strict_height_discount_limit
-- name    : Kyprianou.Ch08.StageB.p2m810_strict_height_discount_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:08:15.548805+00:00
-- url     : https://prove2.me/theorems/cd5c1b42-d9e9-46d0-9cf3-b0ca7945b677
-- title:
--   Discounted strict height survival as a decreasing threshold limit
-- statement:
--   At a finite first upper crossing l>0 the process has no upward overshoot, its drawdown is zero there, and right continuity gives a short interval with drawdown less than a. Thus the event of strict record survival equals the intersection of the strict pre-record height bounds a+1/(k+1). At an infinite upper clock the discount vanishes. Prove measurability and apply bounded convergence to the weighted indicators.
-- source:
--   Kyprianou (2006), Theorems 8.2 and 8.10(i).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Discounted strict height survival as a decreasing threshold limit -/
theorem p2m810_strict_height_discount_limit :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q a l : ℝ), 0 ≤ q → 0 < a → 0 < l →
      Tendsto (fun k : ℕ =>
        ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X l (a + 1 / ((k : ℝ)+1)) ω},
          Real.exp (Phi ψ q * l) * discountedAt q (tauPlus D.X l ω) ∂P)
        atTop (nhds (Real.exp (Phi ψ q * l) *
          (∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X 0 a ω
            then discountedAt q (tauPlus D.X l ω) else 0 ∂P))) := by
  sorry
end Kyprianou.Ch08.StageB
