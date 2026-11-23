-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_small_step_positive
-- name    : Kyprianou.Ch08.StageB.actual_height_small_step_positive
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T08:21:01.357809+00:00
-- url     : https://prove2.me/theorems/8caa791e-d2d6-439f-b551-2f462ed4638e
-- title:
--   Genuine first strict upcrossing with positive normalized no-drawdown survival at a small step
-- statement:
--   For every strictly positive excursion height and nonnegative discount of a source-equivalent spectrally negative Levy model, there exists a strictly positive upward-passage level smaller than that height for which the true original-process normalised no-drawdown discounted integral is strictly positive. This follows from Theorem 8.1 two-sided scale ratios and an excursion drawdown inclusion, not from an assumed height measure.
-- source:
--   Source-faithful first-stage positivity decomposition of canonical Lemma 8.2 actual_height_tail_positivity_independent, deriving the positive small-step event from proved Kyprianou drawdown and exit-ratio lemmas; later use proved actual_height_semigroup to obtain the level-one target.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_small_step_positive
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ h : ℝ, 0 < h →
      ∃ d : ℝ, 0 < d ∧ d < h ∧
        0 < (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d h ω},
          Real.exp (Phi ψ q * d) * discountedAt q (tauPlus D.X d ω) ∂P) := by
  sorry
