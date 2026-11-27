-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45BadLeftPathV1
-- name    : Kyprianou.Ch04.exercise45BadLeftPathV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:10:21.048499+00:00
-- url     : https://prove2.me/theorems/35566b3f-3990-512f-a050-802d31e7db83
-- title:
--   Altered deterministic left path and empty jump measure
-- statement:
--   The altered deterministic left path has the correct positive-time limits and empty jump measure.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), formal boundary audit.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The altered left state has the correct positive-time limits and zero jump measure. -/
theorem Kyprianou.Ch04.exercise45BadLeftPathV1 {m : MeasurableSpace ℕ} (P : @Measure ℕ m) :
    let X : NNReal → ℕ → ℝ := fun t _ => (t : ℝ)
    let Y : NNReal → ℕ → ℝ := fun t w => if t = 0 then (w : ℝ) else (t : ℝ)
    (∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Y t w))) ∧
    (∀ w, Kyprianou.Ch04.pathJumpMeasure X Y w = 0) := by
  sorry
