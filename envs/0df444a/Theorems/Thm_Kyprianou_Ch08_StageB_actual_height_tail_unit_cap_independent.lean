-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_unit_cap_independent
-- name    : Kyprianou.Ch08.StageB.actual_height_tail_unit_cap_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:01:10.074771+00:00
-- url     : https://prove2.me/theorems/4e5ad768-b89c-46d8-91e5-0221038b7df1
-- title:
--   Independent source-faithful unit upper bound for normalized excursion-height survival
-- statement:
--   Upper bound by one of the normalized discounted no-drawdown survival integral; requires unrestricted upward-passage martingale bound valid at all nonnegative discounts, including zero, and source-faithful original model transport. Second conjunct of tail-bounds theorem 7b9a2094.
-- source:
--   Exact conjunct extracted without changing quantifiers or assumptions from canonical Kyprianou.Ch08.StageB.actual_height_tail_bounds, target 7b9a2094-1363-40e2-b3b1-f5bcd128e97f. This is a mathematical decomposition whose parent bridge is conjunction introduction.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_tail_unit_cap_independent
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ h : ℝ, 0 < h →
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) ≤ 1 := by
  sorry
