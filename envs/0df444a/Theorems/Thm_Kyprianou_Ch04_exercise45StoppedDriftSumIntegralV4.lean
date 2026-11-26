-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45StoppedDriftSumIntegralV4
-- name    : Kyprianou.Ch04.exercise45StoppedDriftSumIntegralV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:32:45.736641+00:00
-- url     : https://prove2.me/theorems/9f1764ae-ae47-5373-ab15-b435e54a5918
-- title:
--   exercise45StoppedDriftSumIntegralV4
-- statement:
--   exercise45StoppedDriftSumIntegralV4
-- source:
--   Exercise 4.5: stopped finite cutoff grids

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45StoppedDriftSumIntegralV4
    (T t : NNReal) (n : ℕ) (H : NNReal → ℝ) :
    let u : ℕ → NNReal := fun i => T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
    (∫ s in Ioc (0 : ℝ) (t : ℝ),
      ∑ i ∈ Finset.range (n+1),
        (Ioc (u i : ℝ) (u (i+1) : ℝ)).indicator (fun _ => H (u i)) s) =
      ∑ i ∈ Finset.range (n+1),
        H (u i) * ((min t (u (i+1)) : NNReal).toReal - (min t (u i) : NNReal).toReal) := by
  sorry
