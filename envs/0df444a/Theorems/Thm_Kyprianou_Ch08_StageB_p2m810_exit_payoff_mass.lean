-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_exit_payoff_mass
-- name    : Kyprianou.Ch08.StageB.p2m810_exit_payoff_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:26:02.19422+00:00
-- url     : https://prove2.me/theorems/98e1832a-2d7b-41dd-a846-2f0c0ddf6f0e
-- title:
--   Two-sided exit payoffs have total mass at most one
-- statement:
--   The actual strict upper and lower exit events are disjoint. Their nonnegative discounted payoffs are at most one and are integrable by the existing strict-clock measurability lemma.
-- source:
--   Kyprianou (2006), Theorem 8.10(ii), and Theorem 8.1.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Two-sided exit payoffs have total mass at most one -/
theorem p2m810_exit_payoff_mass :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      0 ≤ downBeforeUpExpectation P D.X q x a ∧
      upBeforeDownExpectation P D.X q x a + downBeforeUpExpectation P D.X q x a ≤ 1 := by
  sorry
end Kyprianou.Ch08.StageB
