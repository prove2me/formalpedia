-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_source_scale_cumulative_nonnegative
-- name    : Kyprianou.Ch08.StageB.p2m85_source_scale_cumulative_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:58:08.025599+00:00
-- url     : https://prove2.me/theorems/ba51b2a4-f2a7-4cc2-9e02-05805c931d5f
-- title:
--   Tilted scale cumulative representation for non-negative discount
-- statement:
--   Tilted scale cumulative representation for non-negative discount
-- source:
--   Kyprianou (2006), Exercise 8.5(i)

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_descending_potential
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_cumulative_continuous
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_cumulative_laplace
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m85_source_scale_cumulative_nonnegative

    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∃ ν : Measure ℝ, ν (Iio (0 : ℝ)) = 0 ∧
      (∀ r : ℝ, ν (Iic r) < ⊤) ∧
      (∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s*y)) ∂ν) =
        ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q))) ∧
      (∀ r : ℝ, Real.exp (-(Phi ψ q) * r) * W q r = (ν (Iic r)).toReal) := by
  sorry
