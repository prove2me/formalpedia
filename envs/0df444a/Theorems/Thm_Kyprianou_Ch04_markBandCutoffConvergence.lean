-- Prove2me | Theorems.Thm_Kyprianou_Ch04_markBandCutoffConvergence
-- name    : Kyprianou.Ch04.markBandCutoffConvergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:34:28.029841+00:00
-- url     : https://prove2.me/theorems/5d7e09d4-8032-4a0c-9c0e-ef1e689f88a9
-- title:
--   markBandCutoffConvergence
-- statement:
--   Finite-band truncation converges both in L2 and real absolute L1 distance for a kernel in L1 and L2.
-- source:
--   Kyprianou (2006), Exercise 4.4, mark-band exhaustion.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Finite-band truncations of a measurable L1 and L2 kernel converge in both norms. -/
theorem Kyprianou.Ch04.markBandCutoffConvergence {A : Type} [MeasurableSpace A] (mu : Measure A)
    (B : ℕ → Set A) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) (hcover : (⋃ n, B n) = Set.univ)
    (g : A → ℝ) (hgi : Integrable g mu) (hg : MemLp g 2 mu) :
    let f := fun n => (B n).indicator g
    let hf : ∀ n, MemLp (f n) 2 mu := fun n => hg.indicator (hB n)
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) ∧
      Tendsto (fun n => ∫ a, |f n a - g a| ∂mu) atTop (𝓝 0) := by
  sorry
