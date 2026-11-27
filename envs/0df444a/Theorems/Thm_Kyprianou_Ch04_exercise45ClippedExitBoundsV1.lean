-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45ClippedExitBoundsV1
-- name    : Kyprianou.Ch04.exercise45ClippedExitBoundsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:11:59.309794+00:00
-- url     : https://prove2.me/theorems/31f80302-1b31-5fe9-803d-7edf1df5913f
-- title:
--   Spatial exit clocks bound the left state through the exit, including time zero.
-- statement:
--   Spatial exit clocks bound the left state through the exit, including time zero.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv).

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45ClippedExitBoundsV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X L : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (hL0 : ∀ᵐ w ∂P, L 0 w = X 0 w) :
    let σ (n : ℕ) (w : Ω) : WithTop NNReal :=
      sInf {v | ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |X u w|}
    let τ (n : ℕ) (w : Ω) : NNReal :=
      (min (σ n w) (n : NNReal)).untopD (n : NNReal)
    ∀ᵐ w ∂P, ∀ n, (∀ t < τ n w, |X t w| ≤ (n : ℝ)) ∧
      (∀ t ≤ τ n w, |L t w| ≤ (n : ℝ)) := by
  sorry
