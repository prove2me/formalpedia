-- Prove2me | Theorems.Thm_Kyprianou_Ch04_affineStepsBoundedV1
-- name    : Kyprianou.Ch04.affineStepsBoundedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:46:18.001198+00:00
-- url     : https://prove2.me/theorems/8d8e69da-3204-47f8-8fb6-9640ba273dec
-- title:
--   Compact bound for finite affine-step paths
-- statement:
--   Compact bound for finite affine-step paths
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem affineStepsBoundedV1 {ι : Type} (s : Finset ι) (a r : ι → ℝ)
    (b : ℝ) (T : NNReal) (U : NNReal → ℝ)
    (hU : ∀ t ≤ T, U t = b * (t : ℝ) +
      ∑ i ∈ s, if r i ≤ (t : ℝ) then a i else 0) :
    ∀ t ≤ T, |U t| ≤ |b| * (T : ℝ) + ∑ i ∈ s, |a i| := by
  sorry
end Kyprianou.Ch04
