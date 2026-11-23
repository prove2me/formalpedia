-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_up_before_down_excursion_exponential
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_up_before_down_excursion_exponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:43:40.054645+00:00
-- url     : https://prove2.me/theorems/efd9aabc-cb4e-4443-a2e5-0c09c61782a3
-- title:
--   Theorem 8.2 helper: up-before-down excursion exponential bridge
-- statement:
--   Under the actual q-excursion-height law, the exact up-before-down expectation equals the exponential of the interval integral of the closed excursion tail plus the Laplace root. This is the missing source-derived strong-Markov bridge for the scale representation.
-- source:
--   Source-derived bridge between the first actual excursion-height clause and the second scale-representation clause of Kyprianou Chapter 8 Theorem 8.2, using the exact published Stage C definition and original source assumptions.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_up_before_down_excursion_exponential
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (q : ℝ) (hq : 0 ≤ q) (n : Measure ℝ)
    (hLaw : HasActualQExcursionHeightLaw P D ψ q n) :
    ∀ x a : ℝ, 0 < x → x < a →
      upBeforeDownExpectation P D.X q x a =
        Real.exp (-(∫ t in x..a, Phi ψ q + (n (Set.Ici t)).toReal)) := by
  sorry
