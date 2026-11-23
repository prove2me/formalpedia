-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_sourceReflectedPathRegularityAE
-- name    : Kyprianou.Ch08.StageB.sourceReflectedPathRegularityAE
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T11:29:28.605274+00:00
-- url     : https://prove2.me/theorems/ad597f58-770f-473c-afa0-c8290c6db343
-- title:
--   Lemma 8.2: original reflected surplus is a.s. right-continuous and upper semicontinuous on each finite clock
-- statement:
--   The reflected path of an original spectrally negative source model has right-continuous sample paths and is upper semicontinuous on every compact nonnegative interval, almost surely under the original probability. This follows from source cadlag and the no-positive-jumps property, via the fact that reflection has no downward jumps. The quantified compact interval is deterministic and independent of any finite stopping-time assumption.
-- source:
--   Source-specific transfer of proved generic AvramDividend.Classical.cadlag_no_downward_jumps_upperSemicontinuousOn_Icc and reflectedSup right-continuity, without assuming Avram and Kyprianou process models are interchangeable. Chapter 8 Lemma 8.2 frontier f9a67c26.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.sourceReflectedPathRegularityAE
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0,
        ContinuousWithinAt
          (fun s : ℝ≥0 => reflectAtSup D.X 0 s ω)
          (Set.Ici t) t) ∧
      (∀ z : ℝ≥0,
        UpperSemicontinuousOn
          (fun s : ℝ≥0 => reflectAtSup D.X 0 s ω)
          (Set.Icc 0 z)) := by
  sorry
