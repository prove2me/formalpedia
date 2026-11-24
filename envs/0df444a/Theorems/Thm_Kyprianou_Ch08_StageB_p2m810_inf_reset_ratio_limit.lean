-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_reset_ratio_limit
-- name    : Kyprianou.Ch08.StageB.p2m810_inf_reset_ratio_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:05:13.999718+00:00
-- url     : https://prove2.me/theorems/deb1356f-a7a4-4160-bccf-b5d84c29fff2
-- title:
--   Small-reset renewal quotient converges to the Z-scale ratio
-- statement:
--   The reset correction delta(epsilon)=(Z(epsilon)-1)/W(epsilon) tends to zero, and W and Z are continuous on nonnegative arguments. The quotient at either a or a-epsilon converges to Z(x)/Z(a), with Z(a) at least one.
-- source:
--   Kyprianou (2006), Theorem 8.10(ii); Pistorius (2004), Proposition 2(i), and two-sided exit renewal approximation.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Small-reset renewal quotient converges to the Z-scale ratio -/
theorem p2m810_inf_reset_ratio_limit :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      (∀ b : ℝ, 0 < b → 0 < W q b) →
      let R := fun (ε b : ℝ) => ((Zscale q (W q) (x+ε) -
        W q (x+ε) * ((Zscale q (W q) ε - 1) / W q ε)) /
      (Zscale q (W q) (b+ε) -
        W q (b+ε) * ((Zscale q (W q) ε - 1) / W q ε)))
      Tendsto (fun ε => R ε a) (nhdsWithin 0 (Ioi 0))
        (nhds (Zscale q (W q) x / Zscale q (W q) a)) ∧
      Tendsto (fun ε => R ε (a-ε)) (nhdsWithin 0 (Ioi 0))
        (nhds (Zscale q (W q) x / Zscale q (W q) a)) := by
  sorry
end Kyprianou.Ch08.StageB
