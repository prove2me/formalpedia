-- Prove2me | Theorems.Thm_Kyprianou_Ch04_markedFullClockAEMeasurable
-- name    : Kyprianou.Ch04.markedFullClockAEMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:30:34.247817+00:00
-- url     : https://prove2.me/theorems/bb0a3286-4f35-4f0b-b9ee-6ff3de9b59ea
-- title:
--   markedFullClockAEMeasurable
-- statement:
--   The full nonnegative predictable random integral is almost everywhere measurable by exhaustion with finite mark bands.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteMarkedClockMeasure
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A full nonnegative predictable random integral is a.e. measurable by finite-band exhaustion. -/
theorem Kyprianou.Ch04.markedFullClockAEMeasurable
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (R : Omega → Measure (ℝ × ℝ))
    (hR : ∀ S : Set (ℝ × ℝ), MeasurableSet S → Measurable (fun w => R w S))
    (t : NNReal) (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) (hcover : (⋃ n, B n) = Set.univ)
    (hFin : ∀ n, ∀ᵐ w ∂P, R w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B n) ≠ ⊤)
    (f : ((NNReal × Omega) × ℝ) → ENNReal)
    (hf : Measurable[F.predictable.prod inferInstance] f) :
    AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
      f ((z.1.toNNReal,w),z.2) ∂(R w)) P := by sorry
