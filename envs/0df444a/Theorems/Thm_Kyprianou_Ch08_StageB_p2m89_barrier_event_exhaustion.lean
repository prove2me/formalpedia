-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_barrier_event_exhaustion
-- name    : Kyprianou.Ch08.StageB.p2m89_barrier_event_exhaustion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T09:49:53.847682+00:00
-- url     : https://prove2.me/theorems/c3249260-9408-448b-8366-d6c968a9a3a8
-- title:
--   Increasing lower survival events exhaust unrestricted occupation
-- statement:
--   Order the lower hitting clocks and use the compact horizon lower bound at t+1, transferring the almost-sure path version.
-- source:
--   Exact decomposition of 50c915ba-2eda-4061-82af-1ed9ac6d0456.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_barrier_event_exhaustion
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) (x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    ∀ t : ℝ≥0,
      let S : ℕ → Set Ω := fun n => {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X (n : ℝ)) 0 ω ∧
        shifted D.X x t ω ∈ A}
      Monotone S ∧ (⋃ n, S n) =ᵐ[P] {ω | shifted D.X x t ω ∈ A} := by
  sorry
