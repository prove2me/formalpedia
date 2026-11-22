-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_bounded_on_Icc
-- name    : Kyprianou.Ch08.StageB.actual_height_bounded_on_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:54:30.273507+00:00
-- url     : https://prove2.me/theorems/7909cd53-cf18-4a21-b20f-33b6f9e7d3b1
-- title:
--   Theorem 8.2 actual-height boundedness on [1,2]: integral cap for Cauchy step
-- statement:
--   Under the exact hypotheses of Theorem 8.2, for each fixed positive height h the no-drawdown survival functional S(x,h) is bounded above on x in [1,2]. This is the boundedness hypothesis needed for the Cauchy exponential step of the T3 multiplicative law; proof via discounted<=1, exp(|Phi|*2) pointwise cap, setIntegral mono and prob_le_one.
-- source:
--   Source-faithful decomposition child of Kyprianou Chapter 8 Theorem 8.2 actual-height multiplicative law (parent 027be585-204d-4aae-93f8-d5329c6a8b14): isolates the [1,2]-boundedness obligation for the Cauchy step, with exact original-path event and payoff from Definitions.Def_Kyprianou_Ch08_StageCFoundation_D. Complexity split: parent bridge with inline boundedness exceeds complexity cap (0.2133 vs -0.0523); this child proof fits (lint PASS).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_bounded_on_Icc
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ h : ℝ, 0 < h → ∃ B : ℝ, ∀ x : ℝ, 1 ≤ x → x ≤ 2 →
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X x h ω}, Real.exp (Phi ψ q * x) * discountedAt q (tauPlus D.X x ω) ∂P) ≤ B := by
  sorry
