-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_scale_slope_nonnegative
-- name    : Kyprianou.Ch08.StageB.p2m810_scale_slope_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:21:34.768286+00:00
-- url     : https://prove2.me/theorems/896ffe2f-9270-4675-aaa3-88e22416e877
-- title:
--   Positive scale and nonnegative right derivative
-- statement:
--   The proved Theorem 8.2 supplies positivity and expresses the right derivative as (Phi(q)+strict excursion tail)*W(a).
-- source:
--   Kyprianou (2006), Theorem 8.10(i), record renewal; Theorem 8.2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Positive scale and nonnegative right derivative -/
theorem p2m810_scale_slope_nonnegative :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      0 < W q a ∧ 0 ≤ derivWithin (W q) (Ici a) a := by
  sorry
end Kyprianou.Ch08.StageB
