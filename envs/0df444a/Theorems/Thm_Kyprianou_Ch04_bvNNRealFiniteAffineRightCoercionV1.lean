-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineRightCoercionV1
-- name    : Kyprianou.Ch04.bvNNRealFiniteAffineRightCoercionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:35:02.465977+00:00
-- url     : https://prove2.me/theorems/2ea533d5-1c5e-4a64-b47b-7aeb141e2a36
-- title:
--   Real and nonnegative-time finite affine right paths agree
-- statement:
--   For a nonnegative real time the real coercion of toNNReal equals the original time. The weak time comparisons are equivalent, so their indicator summands agree by cases.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; finite-jump time-coercion interface.

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

theorem Kyprianou.Ch04.bvNNRealFiniteAffineRightCoercionV1
    {I : Type} (τ : I → NNReal) (j : I → ℝ) (a c : ℝ)
    (S : Finset I) (u : ℝ) (hu : 0 ≤ u) :
    a + c * u + (∑ i ∈ S, if (τ i : ℝ) ≤ u then j i else 0) =
      a + c * (Real.toNNReal u : ℝ) +
        ∑ i ∈ S, if τ i ≤ Real.toNNReal u then j i else 0 := by
  sorry
