-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sup_discounted_record_integral
-- name    : Kyprianou.Ch08.StageB.p2m810_sup_discounted_record_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:05:01.259431+00:00
-- url     : https://prove2.me/theorems/3ca6c4cd-36bc-46cf-8493-a4ea5904dae1
-- title:
--   Discounted upper record integral before actual strict drawdown
-- statement:
--   Integrate the discounted upper crossing probabilities of actual record levels above the initial maximum, killed at the strict drawdown. The integral equals the original scale divided by its nonzero right derivative. Derive using the strict-threshold height law and strong Markov at the first record x.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); Avram, Kyprianou and Pistorius (2004), section 4, equations (13)-(22).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Discounted upper record integral before actual strict drawdown -/
theorem p2m810_sup_discounted_record_integral :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      derivWithin (W q) (Ici a) a ≠ 0 →
      (∫ l in Ioi x, ∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X x a ω
          then discountedAt q (tauPlus D.X l ω) else 0 ∂P) = W q (a-x) / derivWithin (W q) (Ici a) a := by
  sorry
end Kyprianou.Ch08.StageB
