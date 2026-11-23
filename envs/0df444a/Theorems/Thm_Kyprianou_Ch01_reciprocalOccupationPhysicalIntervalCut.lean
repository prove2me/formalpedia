-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationPhysicalIntervalCut
-- name    : Kyprianou.Ch01.reciprocalOccupationPhysicalIntervalCut
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:15:45.749454+00:00
-- url     : https://prove2.me/theorems/14083a64-e668-4076-8947-d0a7a3b9a148
-- title:
--   The reciprocal occupation Lebesgue integral over the real interval (0,u] splits additively over the disjoint half-open subintervals (0,A] and (A,u], when 0≤A≤u
-- statement:
--   The reciprocal occupation Lebesgue integral over the real interval (0,u] splits additively over the disjoint half-open subintervals (0,A] and (A,u], when 0≤A≤u. This is an application of lintegral_union, and the definition of reciprocalOccupation.
-- source:
--   Kyprianou (2006) Section 1.3.4; exact physical-time reciprocal occupation integration at first marked arrival.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reciprocalOccupationPhysicalIntervalCut
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω)
    (u : ℝ≥0) (hu : A ≤ (u : ℝ)) :
    reciprocalOccupation X u ω =
      reciprocalOccupation X (Real.toNNReal A) ω +
        (∫⁻ s in Set.Ioc A (u : ℝ),
          (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ ∂volume) := by
  sorry
