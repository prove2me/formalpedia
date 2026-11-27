-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45ClippedExitStoppingV1
-- name    : Kyprianou.Ch04.exercise45ClippedExitStoppingV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:11:56.774211+00:00
-- url     : https://prove2.me/theorems/d98b11be-dcd0-5026-b76b-d3aaf981bb1c
-- title:
--   Each finite clipped spatial exit is a stopping time.
-- statement:
--   Each finite clipped spatial exit is a stopping time.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv).

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45ClippedExitStoppingV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hAdapt : Adapted F X) :
    let σ (n : ℕ) (w : Ω) : WithTop NNReal :=
      sInf {v | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |X u w|}
    let τ (n : ℕ) (w : Ω) : NNReal :=
      (min (σ n w) (n : NNReal)).untopD (n : NNReal)
    ∀ n, IsStoppingTime F (fun w => (τ n w : WithTop NNReal)) := by
  sorry
