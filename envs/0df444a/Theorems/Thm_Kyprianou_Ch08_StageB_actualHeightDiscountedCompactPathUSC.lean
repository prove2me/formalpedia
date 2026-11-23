-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightDiscountedCompactPathUSC
-- name    : Kyprianou.Ch08.StageB.actualHeightDiscountedCompactPathUSC
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:05:06.787322+00:00
-- url     : https://prove2.me/theorems/3fc8f83c-bf5a-4a35-bbc5-c1eb01045c2e
-- title:
--   Lemma 8.2: genuine discounted finite upward passage admits upper semicontinuous reflected path ending at zero
-- statement:
--   For the actual spectrally negative model on its original probability space, on an almost-sure event, every sample path having nonzero discounted payoff at first unit upward passage has a strictly positive finite passage time, and its reflected drawdown path is upper semicontinuous on the closed interval from zero to passage, with reflected endpoints zero. These are the exact model-specific geometric conditions required to apply compact excursion-height attainment. Proving them must derive from the genuine process and avoid replacing the law by an abstract measure.
-- source:
--   Kyprianou 2006 Chapter 8 Lemma 8.2, physical PDF p228; exact source model from published Chapter 8 foundations. Parent source obligation cade7bf0-28cb-43f9-b50a-18cc573d5092. Existing proved Avram reflected-geometry statements are leads only and require verified model transfer.

import Mathlib.Topology.Semicontinuity.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actualHeightDiscountedCompactPathUSC
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (q : ℝ) :
    ∀ᵐ ω ∂P, discountedAt q (tauPlus D.X 1 ω) ≠ 0 →
      ∃ ζ : ℝ≥0, 0 < ζ ∧
        tauPlus D.X 1 ω = (ζ : WithTop ℝ≥0) ∧
        UpperSemicontinuousOn
          (fun t : ℝ≥0 => reflectAtSup D.X 0 t ω) (Set.Icc 0 ζ) ∧
        reflectAtSup D.X 0 0 ω = 0 ∧
        reflectAtSup D.X 0 ζ ω = 0 := by
  sorry
