-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_record_survival_pointwise
-- name    : Kyprianou.Ch08.StageB.p2m810_record_survival_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:21:32.769056+00:00
-- url     : https://prove2.me/theorems/609ac777-c81a-46c6-997e-4d2cd1211c4e
-- title:
--   Strict drawdown discounted record survival transform
-- statement:
--   For l>x, the initial first record survival from surplus a-x contributes W(a-x)/W(a); regeneration at record x contributes the strict drawdown exponential transform with rate W'_+(a)/W(a). Derive the latter from Theorem 8.2 by increasing the height threshold down to a, taking care of equality at the upper record.
-- source:
--   Kyprianou (2006), Theorem 8.10(i), record renewal; Theorem 8.2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Strict drawdown discounted record survival transform -/
theorem p2m810_record_survival_pointwise :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ l : ℝ, x < l →
        (∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X x a ω
          then discountedAt q (tauPlus D.X l ω) else 0 ∂P) =
        W q (a-x) / W q a *
          Real.exp (-(derivWithin (W q) (Ici a) a / W q a) * (l-x)) := by
  sorry
end Kyprianou.Ch08.StageB
