-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_barrier_sections_measurable
-- name    : Kyprianou.Ch08.StageB.p2m89_barrier_sections_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T09:50:00.963205+00:00
-- url     : https://prove2.me/theorems/e0981940-162d-4cfe-a736-6306ad49abf1
-- title:
--   Translated killed occupation section measurability
-- statement:
--   Apply the established half-line occupation section measurability with the state set translated by the difference of the starting levels.
-- source:
--   Exact decomposition of 50c915ba-2eda-4061-82af-1ed9ac6d0456.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_barrier_sections_measurable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) (x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    ∀ n : ℕ, Measurable (fun t : ℝ≥0 => P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X (n : ℝ)) 0 ω ∧
        shifted D.X x t ω ∈ A}) := by
  sorry
