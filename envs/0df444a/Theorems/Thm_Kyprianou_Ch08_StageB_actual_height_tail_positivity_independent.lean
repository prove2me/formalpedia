-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_positivity_independent
-- name    : Kyprianou.Ch08.StageB.actual_height_tail_positivity_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:00:59.979247+00:00
-- url     : https://prove2.me/theorems/85ad9894-7b95-48d6-b681-4d5fb4aa3618
-- title:
--   Independent source-faithful strict positive normalized excursion-height survival
-- statement:
--   Strict positivity of the original normalized discounted no-drawdown survival integral at all positive excursion heights, proved from the genuine two-sided exit scale ratio, drawdown inclusion and semigroup. Required as first conjunct of tail-bounds theorem 7b9a2094; independent of the actual height-law existence and its blocked verifier.
-- source:
--   Exact conjunct extracted without changing quantifiers or assumptions from canonical Kyprianou.Ch08.StageB.actual_height_tail_bounds, target 7b9a2094-1363-40e2-b3b1-f5bcd128e97f. This is a mathematical decomposition whose parent bridge is conjunction introduction.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_tail_positivity_independent
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ h : ℝ, 0 < h →
      0 < (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) := by
  sorry
