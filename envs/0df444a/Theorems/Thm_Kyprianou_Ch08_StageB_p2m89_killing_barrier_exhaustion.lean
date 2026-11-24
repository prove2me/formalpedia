-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_killing_barrier_exhaustion
-- name    : Kyprianou.Ch08.StageB.p2m89_killing_barrier_exhaustion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T08:18:58.527449+00:00
-- url     : https://prove2.me/theorems/50c915ba-2eda-4061-82af-1ed9ac6d0456
-- title:
--   Remove the lower killing barrier
-- statement:
--   Pathwise compact-horizon lower bounds exhaust the survival events, and monotone convergence removes the killing barrier.
-- source:
--   Kyprianou (2006), Corollary 8.9; corrected occupation identity 33cf8321-6b73-409d-84cc-a8da6fcb2949.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_killing_barrier_exhaustion
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) (x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    Tendsto (fun n : ℕ => (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
      P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X (n : ℝ)) 0 ω ∧
        shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue)) atTop (𝓝 (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
      P {ω | shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue)) := by
  sorry
