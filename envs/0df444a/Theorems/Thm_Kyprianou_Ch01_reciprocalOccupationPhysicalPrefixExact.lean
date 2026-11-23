-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationPhysicalPrefixExact
-- name    : Kyprianou.Ch01.reciprocalOccupationPhysicalPrefixExact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:15:46.556967+00:00
-- url     : https://prove2.me/theorems/8493bbfb-250b-4d06-84c5-cbb3ab6e5324
-- title:
--   The reciprocal occupation clock at physical time A has value A/y if X is the positive constant integer y strictly before A
-- statement:
--   The reciprocal occupation clock at physical time A has value A/y if X is the positive constant integer y strictly before A. The endpoint A has zero Lebesgue measure. This requires integrating a constant reciprocal against real Lebesgue volume on the half-open interval.
-- source:
--   Kyprianou (2006) Section 1.3.4; exact physical-time reciprocal occupation integration at first marked arrival.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reciprocalOccupationPhysicalPrefixExact
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    reciprocalOccupation X (Real.toNNReal A) ω =
      ENNReal.ofReal (A / (y : ℝ)) := by
  sorry
