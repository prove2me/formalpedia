-- Prove2me | Theorems.Thm_Kyprianou_Ch04_supportedPhysicalWindowClampV1
-- name    : Kyprianou.Ch04.supportedPhysicalWindowClampV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:24:02.202452+00:00
-- url     : https://prove2.me/theorems/5cda6d33-ef9b-442a-be84-7eb076d4a9c7
-- title:
--   Finite-support physical window and clamped kernel equality
-- statement:
--   Restrict a supported marked kernel to its finite mark band and clamp the time at the horizon without changing its physical integral.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem supportedPhysicalWindowClampV1 {Ω : Type} (R : Measure (ℝ × ℝ)) (T : NNReal)
    (B : Set ℝ) (hB : MeasurableSet B)
    (g : (NNReal × Ω) × ℝ → ℝ) (hs : ∀ p, p.2 ∉ B → g p = 0) (ω : Ω) :
    (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ),
      g ((z.1.toNNReal,ω),z.2) ∂ R) =
    ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ B, g ((min z.1.toNNReal T,ω),z.2) ∂ R := by
  sorry
end Kyprianou.Ch04
