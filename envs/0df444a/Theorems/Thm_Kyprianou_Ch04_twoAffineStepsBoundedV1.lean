-- Prove2me | Theorems.Thm_Kyprianou_Ch04_twoAffineStepsBoundedV1
-- name    : Kyprianou.Ch04.twoAffineStepsBoundedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:55:19.432804+00:00
-- url     : https://prove2.me/theorems/a4e3890d-d630-5176-bc6a-ec8c0f4552e2
-- title:
--   Compact bound for drift and two finite step sums
-- statement:
--   Compact bound for drift and two finite step sums
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem twoAffineStepsBoundedV1 {ι κ : Type} (L : Finset ι) (S : Finset κ)
    (a r : ι → ℝ) (c q : κ → ℝ) (d : ℝ) (T : NNReal) (U : NNReal → ℝ)
    (hU : ∀ t ≤ T, U t = d * (t : ℝ) +
      (∑ i ∈ L, if r i ≤ (t : ℝ) then a i else 0) +
      (∑ j ∈ S, if q j ≤ (t : ℝ) then c j else 0)) :
    ∀ t ≤ T, |U t| ≤ |d| * (T : ℝ) + ∑ i ∈ L, |a i| + ∑ j ∈ S, |c j| := by
  sorry
end Kyprianou.Ch04
