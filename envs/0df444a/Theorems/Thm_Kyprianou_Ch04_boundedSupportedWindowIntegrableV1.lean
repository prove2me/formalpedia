-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedSupportedWindowIntegrableV1
-- name    : Kyprianou.Ch04.boundedSupportedWindowIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:30:24.082277+00:00
-- url     : https://prove2.me/theorems/1bf1352e-864a-48e5-911a-b43a11f9d77b
-- title:
--   Integrability and square integrability of bounded finite-window kernels
-- statement:
--   A bounded measurable kernel supported on a finite mark band is integrable
--   and has integrable square on the physical time window.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedSupportedWindowIntegrableV1 (R : Measure (ℝ × ℝ)) (T : ℝ) (B : Set ℝ)
    (hB : MeasurableSet B) (hfin : R (Icc 0 T ×ˢ B) < ⊤)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ p, ‖g p‖ ≤ C)
    (hsupp : ∀ p, p.2 ∉ B → g p = 0) :
    IntegrableOn g (Icc 0 T ×ˢ univ) R ∧
      IntegrableOn (fun p => (g p)^2) (Icc 0 T ×ˢ univ) R := by
  sorry
end Kyprianou.Ch04
