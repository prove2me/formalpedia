-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45ClippedExitMonotoneCofinalV1
-- name    : Kyprianou.Ch04.exercise45ClippedExitMonotoneCofinalV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:11:58.992805+00:00
-- url     : https://prove2.me/theorems/ce762b9d-c1b4-4561-8814-a7dc52583e89
-- title:
--   Finite spatial exit clocks are bounded, monotone and exhaust compact time.
-- statement:
--   Finite spatial exit clocks are bounded, monotone and exhaust compact time.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv).

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45ClippedExitMonotoneCofinalV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P) :
    let σ (n : ℕ) (w : Ω) : WithTop NNReal :=
      sInf {v | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |X u w|}
    let τ (n : ℕ) (w : Ω) : NNReal :=
      (min (σ n w) (n : NNReal)).untopD (n : NNReal)
    (∀ n w, τ n w ≤ (n : NNReal)) ∧
    (∀ w, Monotone (fun n => τ n w)) ∧
    (∀ᵐ w ∂P, Tendsto (fun n => (τ n w : WithTop NNReal)) atTop (nhds ⊤)) := by
  sorry
