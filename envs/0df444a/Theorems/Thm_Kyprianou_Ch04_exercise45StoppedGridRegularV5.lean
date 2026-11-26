-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45StoppedGridRegularV5
-- name    : Kyprianou.Ch04.exercise45StoppedGridRegularV5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T21:42:21.404924+00:00
-- url     : https://prove2.me/theorems/e4eb895d-f3f1-5790-920f-888199ad4fb0
-- title:
--   Stopped weighted grids inherit measurable coordinates and right continuity
-- statement:
--   Stopped weighted grids inherit measurable coordinates and right continuity
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii)

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45StoppedGridRegularV5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y H : NNReal → Ω → ℝ)
    (hmY : ∀ t, AEMeasurable (Y t) P) (hmH : ∀ t, AEMeasurable (H t) P)
    (hrY : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t)
    (T : NNReal) (K : ℝ) :
    let G : ℕ → NNReal → Ω → ℝ := fun n t w =>
      ∑ k ∈ Finset.range n, H (T * (k : NNReal) / (n : NNReal)) w *
        (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
         Y (min t (T * (k : NNReal) / (n : NNReal))) w)
    let R : ℕ → NNReal → Ω → ℝ := fun n t w =>
      K * |Y (min t (T / (n : NNReal))) w - Y 0 w|
    (∀ n t, AEMeasurable (G n t) P ∧ AEMeasurable (R n t) P) ∧
      (∀ᵐ w ∂P, ∀ n t, ContinuousWithinAt (fun s => G n s w) (Ici t) t ∧
        ContinuousWithinAt (fun s => R n s w) (Ici t) t) := by
  sorry
