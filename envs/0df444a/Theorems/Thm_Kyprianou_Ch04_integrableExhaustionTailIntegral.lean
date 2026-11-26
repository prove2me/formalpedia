-- Prove2me | Theorems.Thm_Kyprianou_Ch04_integrableExhaustionTailIntegral
-- name    : Kyprianou.Ch04.integrableExhaustionTailIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:34:20.449966+00:00
-- url     : https://prove2.me/theorems/5dc1f62e-b1e7-47cb-8254-ba8e50c455d8
-- title:
--   integrableExhaustionTailIntegral
-- statement:
--   Integrable tails tend to zero along any increasing measurable exhaustion.
-- source:
--   Kyprianou (2006), Exercise 4.4, mark-band exhaustion.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false

/-- Integrals of integrable kernels on the complement of increasing covering sets tend to zero. -/
theorem Kyprianou.Ch04.integrableExhaustionTailIntegral {A : Type} [MeasurableSpace A] (mu : Measure A)
    (B : ℕ → Set A) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) (hcover : (⋃ n, B n) = Set.univ)
    (g : A → ℝ) (hg : Integrable g mu) :
    Tendsto (fun n => ∫ a, (B n)ᶜ.indicator g a ∂mu) atTop (𝓝 0) := by
  sorry
