-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45FiniteCofinalStopsV1
-- name    : Kyprianou.Ch04.exercise45FiniteCofinalStopsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:04:36.131473+00:00
-- url     : https://prove2.me/theorems/ed114f7f-54c1-5765-a0bf-42df60f2aac6
-- title:
--   Finite cofinal spatial stops for a Levy process
-- statement:
--   Finite deterministic clipping of nested spatial exits exhausts compact clocks and bounds pre-exit states and left limits including at exit.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv).

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Increasing finite spatial exits bound the physical left state through the exit itself. -/
theorem Kyprianou.Ch04.exercise45FiniteCofinalStopsV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (X L : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hAdapt : Adapted F X)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (hL0 : ∀ᵐ w ∂P, L 0 w = X 0 w) :
    ∃ τ : ℕ → Ω → NNReal,
      (∀ n w, τ n w ≤ (n : NNReal)) ∧
      (∀ n, IsStoppingTime F (fun w => (τ n w : WithTop NNReal))) ∧
      (∀ w, Monotone (fun n => τ n w)) ∧
      (∀ᵐ w ∂P, Tendsto (fun n => (τ n w : WithTop NNReal)) atTop (nhds ⊤)) ∧
      (∀ᵐ w ∂P, ∀ n, (∀ t < τ n w, |X t w| ≤ (n : ℝ)) ∧
        (∀ t ≤ τ n w, |L t w| ≤ (n : ℝ))) := by
  sorry
