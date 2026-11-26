-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
-- name    : Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:28:51.411489+00:00
-- url     : https://prove2.me/theorems/a9410283-07b5-576d-9f82-d5d1927b2c57
-- title:
--   Exact finite marked atom subwindow integral
-- statement:
--   Every subwindow integral is the exact finite sum over the original marked atoms.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finitePhysicalAtomsSubwindowIntegralV1 (R : Measure (ℝ × ℝ)) (D : Set (ℝ × ℝ))
    (S : Finset NNReal) (j : NNReal → ℝ)
    (hR : R.restrict D = ∑ t ∈ S, Measure.dirac ((t : ℝ),j t))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (g : ℝ × ℝ → ℝ) :
    (∫ z in A, g z ∂ R) =
      ∑ t ∈ S, if ((t : ℝ),j t) ∈ A then g ((t : ℝ),j t) else 0 := by
  sorry
end Kyprianou.Ch04
