-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineLeftCoercionV1
-- name    : Kyprianou.Ch04.bvNNRealFiniteAffineLeftCoercionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:35:01.749803+00:00
-- url     : https://prove2.me/theorems/3041b9eb-033b-4ddd-b670-0c90c6aa4454
-- title:
--   Real and nonnegative-time finite affine left paths agree
-- statement:
--   The strict time comparison is preserved under the real coercion. Use the same truth value for both indicators to avoid mismatched decidability instances.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; finite-jump time-coercion interface.

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

theorem Kyprianou.Ch04.bvNNRealFiniteAffineLeftCoercionV1
    {I : Type} (τ : I → NNReal) (j : I → ℝ) (a c : ℝ)
    (S : Finset I) (u : NNReal) :
    a + c * (u : ℝ) + (∑ i ∈ S, if (τ i : ℝ) < (u : ℝ) then j i else 0) =
      a + c * (u : ℝ) + ∑ i ∈ S, if τ i < u then j i else 0 := by
  sorry
