-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedFiniteSupportMemLpV1
-- name    : Kyprianou.Ch04.boundedFiniteSupportMemLpV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:07:02.510202+00:00
-- url     : https://prove2.me/theorems/f96dcf39-b6e4-520f-8b12-0565cd34cf19
-- title:
--   Bounded finite-support kernels are integrable and square integrable
-- statement:
--   Bounded measurable kernels supported on a finite-measure set are integrable and square-integrable.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedFiniteSupportMemLpV1 {A : Type} [MeasurableSpace A]
    (μ : Measure A) (S : Set A) (hS : MeasurableSet S) (hfin : μ S < ⊤)
    (g : A → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ p, ‖g p‖ ≤ C)
    (hsupp : ∀ p, p ∉ S → g p = 0) :
    Integrable g μ ∧ MemLp g 2 μ := by
  sorry
end Kyprianou.Ch04
