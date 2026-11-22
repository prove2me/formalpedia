-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
-- name    : Kyprianou.Ch08.StageB.source_result81_filtered_avram_model
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:40:02.569234+00:00
-- url     : https://prove2.me/theorems/297b1fce-72b0-452b-a84f-3c5e7a59fe1e
-- title:
--   Filtered all-path realization of the Chapter 8 Lévy source
-- statement:
--   Realize the same Lévy process in an everywhere regular model with the raw natural filtration. The path versions agree at all times outside one null event and the two Laplace exponents agree for every nonnegative argument.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1. Source-faithful decomposition of b5430c32-5738-4ad5-9956-e8891a1d6407.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_filtered_avram_model
    (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) :
    ∃ (F : Filtration ℝ≥0 mΩ)
      (A : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      (∀ᵐ ω ∂P, ∀ t, A.X t ω = D.X t ω) ∧
      (∀ β : ℝ, 0 ≤ β → A.ψ β = ψ β) := by
  sorry
