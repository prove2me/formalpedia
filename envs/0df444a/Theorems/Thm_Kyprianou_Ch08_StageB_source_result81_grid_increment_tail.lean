-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_grid_increment_tail
-- name    : Kyprianou.Ch08.StageB.source_result81_grid_increment_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:58:54.62512+00:00
-- url     : https://prove2.me/theorems/fd810259-f45c-40a9-888d-281dee17979f
-- title:
--   Exponential tail bound for a fine-grid Lévy increment
-- statement:
--   For a spectrally negative triplet with a quadratic upper bound on the real exponent, an increment over an interval of length r⁻⁴ has probability at most exp(K−r) of exceeding r⁻¹, for r at least one.
-- source:
--   Auxiliary lemma for the spectral-negativity step in Kyprianou (2006), Chapter 8, Theorem 8.1. Parent Prove2Me theorem 92200ffc-acdc-4836-b709-dd420298cdde.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_grid_increment_tail
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (K : ℝ)
    (hK : ∀ b : ℝ, 1 ≤ b → tripletLaplace (-D.triplet.drift) D.gaussianCoefficient
      D.triplet.levyMeasure b ≤ K * b ^ 2)
    (s : ℝ≥0) (r : ℝ) (hr : 1 ≤ r) (d : ℝ≥0) (hd : (d : ℝ) = (r ^ 4)⁻¹) :
    P {ω | r⁻¹ ≤ D.X (s + d) ω - D.X s ω} ≤ ENNReal.ofReal (Real.exp (K - r)) := by
  sorry
