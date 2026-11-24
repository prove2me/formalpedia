-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_first_cycle_inequalities
-- name    : Kyprianou.Ch08.StageB.p2m810_inf_first_cycle_inequalities
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:26:13.35043+00:00
-- url     : https://prove2.me/theorems/657b5607-6a2a-4874-b7d2-1f08b9ecfa3e
-- title:
--   First-cycle renewal inequalities for actual infimum reflection
-- statement:
--   Stop the unreflected increment upon first exiting (-epsilon,b), relative to its initial reference minimum -x. Before the lower exit, its height above the reference differs from the actual reflected height by a number in [0,epsilon]. At the lower exit the actual reflected process restarts at zero. Strong Markov and discount monotonicity give the lower inequality at b=a and the upper inequality at b=a-epsilon; the upper payoff is at most one. Handle both infinite clocks and all strict endpoint conventions.
-- source:
--   Kyprianou (2006), Theorem 8.10(ii), and Theorem 8.1.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- First-cycle renewal inequalities for actual infimum reflection -/
theorem p2m810_inf_first_cycle_inequalities :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      let F := fun y : ℝ => ∫ ω, discountedAt q (reflectedInfExit D.X y a ω) ∂P
      let A := fun (ε b y : ℝ) => upBeforeDownExpectation P D.X q (y+ε) (b+ε)
      let B := fun (ε b y : ℝ) => downBeforeUpExpectation P D.X q (y+ε) (b+ε)
      F x ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < a →
        A ε a x + B ε a x * F 0 ≤ F x ∧
        (x ≤ a-ε → F x ≤ A ε (a-ε) x + B ε (a-ε) x * F 0) := by
  sorry
end Kyprianou.Ch08.StageB
