-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_actual_rate_exp_law
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_actual_rate_exp_law
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T17:43:37.612959+00:00
-- url     : https://prove2.me/theorems/c6314c52-5319-478c-9e31-3954b0144d45
-- title:
--   Theorem 8.2 helper: positive-height excursion-rate law
-- statement:
--   For the exact model and scale-family hypotheses of Theorem 8.2, the actual no-drawdown rate on positive heights has a nonnegative decreasing right-continuous tail exponent tending to zero at infinity. Its left limit gives the closed-tail exponent in the discounted original-path identity, so atoms are retained.
-- source:
--   Source-derived analytic bridge isolating the actual positive-height excursion-rate law needed to construct the first measure in sourceCertificate_result8_2, from the exact original Kyprianou Chapter 8 Theorem 8.2 source and its published Stage C definition. The right-continuous open-tail exponent uses a left limit for closed tails, preserving atoms.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_actual_rate_exp_law
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ F : ℝ → ℝ,
      (∀ h : ℝ, 0 < h → 0 ≤ F h) ∧
      AntitoneOn F (Set.Ioi (0 : ℝ)) ∧
      (∀ h : ℝ, 0 < h → ContinuousWithinAt F (Set.Ici h) h) ∧
      Tendsto F atTop (nhds (0 : ℝ)) ∧
      (∀ a h : ℝ, 0 < a → 0 < h →
        (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a h ω},
          Real.exp (Phi ψ q * a) * discountedAt q (tauPlus D.X a ω) ∂P)
          = Real.exp (-a * Function.leftLim F h)) := by
  sorry
