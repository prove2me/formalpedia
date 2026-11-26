-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45GridL1StepErrorV4
-- name    : Kyprianou.Ch04.exercise45GridL1StepErrorV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:31:16.858711+00:00
-- url     : https://prove2.me/theorems/ce8ebf09-8124-4d6e-bb05-428258a4ab22
-- title:
--   exercise45GridL1StepErrorV4
-- statement:
--   exercise45GridL1StepErrorV4
-- source:
--   Exercise 4.5: stopped finite cutoff grids

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45GridL1StepErrorV4
    (T : NNReal) (H : NNReal → ℝ) (C : ℝ)
    (hb : ∀ r, |H r| ≤ C)
    (hl : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r))) :
    let u : ℕ → ℕ → NNReal := fun n i => T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
    let G : ℕ → ℝ → ℝ := fun n s => ∑ i ∈ Finset.range (n+1),
      (Ioc (u n i : ℝ) (u n (i+1) : ℝ)).indicator (fun _ => H (u n i)) s
    (∀ n, Integrable (G n) (volume.restrict (Ioc (0 : ℝ) (T : ℝ)))) ∧
    Integrable (fun s : ℝ => H s.toNNReal) (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) ∧
    Tendsto (fun n => ∫ s in Ioc (0 : ℝ) (T : ℝ), |G n s - H s.toNNReal|)
      atTop (𝓝 0) := by
  sorry
