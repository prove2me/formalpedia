-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_cycle_path_comparison
-- name    : Kyprianou.Ch08.StageB.p2m810_inf_cycle_path_comparison
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:16:06.335104+00:00
-- url     : https://prove2.me/theorems/89e6ef1b-ec79-406b-ae65-701fa182fc7b
-- title:
--   Infimum-reflected exit compared with fresh-path cycle payoffs
-- statement:
--   The original reflected height before lower exit differs from unreflected height above the initial reference minimum by a nonnegative amount at most epsilon. At finite lower exit the reference is replaced by the new running minimum; if exit has not already occurred, the actual residual path equals the fresh reflected path. Compare discount payoffs on each exit event using the two thresholds a and a-epsilon, including infinite clocks, and integrate. This uses no conditional independence or renewal factorisation.
-- source:
--   Kyprianou (2006), Theorem 8.10(ii), and Theorem 8.1.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Infimum-reflected exit compared with fresh-path cycle payoffs -/
theorem p2m810_inf_cycle_path_comparison :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ ε : ℝ, 0 < ε → ε < a →
      let C := fun (b : ℝ) (ω : Ω) =>
        let u := tauPlus (shifted D.X (x+ε)) (b+ε) ω
        let v := tauMinus (shifted D.X (x+ε)) 0 ω
        let r : ℝ≥0 := match v with
          | ⊤ => 0
          | (s : ℝ≥0) => s
        if u < v then discountedAt q u else
          if v < u then discountedAt q v *
            discountedAt q (reflectedInfExit
              (fun t w => D.X (r+t) w - D.X r w) 0 a ω)
          else 0
      let F := ∫ ω, discountedAt q (reflectedInfExit D.X x a ω) ∂P
      (∫ ω, C a ω ∂P) ≤ F ∧
        (x ≤ a-ε → F ≤ ∫ ω, C (a-ε) ω ∂P) := by
  sorry
end Kyprianou.Ch08.StageB
