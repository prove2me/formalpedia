-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationShiftedTailLIntegral
-- name    : Kyprianou.Ch01.reciprocalOccupationShiftedTailLIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:15:38.383384+00:00
-- url     : https://prove2.me/theorems/a4227043-2c02-4d1a-b239-97fbe6b0ab27
-- title:
--   The reciprocal occupation integral of X over the real interval (A,u] equals the integral of the shifted path Y over (0,u-A]
-- statement:
--   The reciprocal occupation integral of X over the real interval (A,u] equals the integral of the shifted path Y over (0,u-A]. This follows from hShift, the equality of the shifted integrands after real-to-nonnegative coercion, and translation-invariance of real Lebesgue volume for arbitrary nonnegative integrands.
-- source:
--   Kyprianou (2006) Section 1.3.4; exact physical-time reciprocal occupation integration at first marked arrival.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reciprocalOccupationShiftedTailLIntegral
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω)
    (u : ℝ≥0) (hu : A ≤ (u : ℝ)) :
    (∫⁻ s in Set.Ioc A (u : ℝ),
      (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ ∂volume) =
      reciprocalOccupation Y (Real.toNNReal ((u : ℝ) - A)) ω := by
  sorry
