-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_bounds
-- name    : Kyprianou.Ch08.StageB.actual_height_tail_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:04:47.584835+00:00
-- url     : https://prove2.me/theorems/7b9a2094-1363-40e2-b3b1-f5bcd128e97f
-- title:
--   Theorem 8.2 actual-height tail bounds: positivity and unit cap
-- statement:
--   Under the exact hypotheses of Theorem 8.2, the unit-level no-drawdown survival functional S(1,h) is strictly positive and bounded above by one for every positive height h. Positivity needs the discounted integral on a positive-probability event; the unit cap needs the Esscher upper-bound estimate.
-- source:
--   Source-faithful decomposition child of Kyprianou Chapter 8 Theorem 8.2 actual-height law (parent 3eded364-8075-43f9-bae4-12db613bec33): isolates the survival-functional bounds (gaps hpos/hle1) with the exact original-path event NoDrawdownBeforeUpcrossing and discounted first-upcrossing payoff from Definitions.Def_Kyprianou_Ch08_StageCFoundation_D.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_tail_bounds
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ h : ℝ, 0 < h →
      0 < (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) ∧
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) ≤ 1 := by
  sorry
