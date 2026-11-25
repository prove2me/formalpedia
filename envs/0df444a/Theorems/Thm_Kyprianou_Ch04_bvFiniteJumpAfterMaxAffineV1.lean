-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpAfterMaxAffineV1
-- name    : Kyprianou.Ch04.bvFiniteJumpAfterMaxAffineV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:13:09.748262+00:00
-- url     : https://prove2.me/theorems/a905d54e-8e68-42f0-a91d-2c8d96211046
-- title:
--   Affine path after the largest retained jump
-- statement:
--   After the largest retained jump all retained jumps are included in the constant intercept.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic finite-jump telescoping.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvFiniteJumpAfterMaxAffineV1
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (S : Finset I) (k : I) (hk : ∀ s ∈ S, s < k) (u : ℝ) (hu : τ k ≤ u) :
    a + d * u + ∑ s ∈ insert k S, (if τ s ≤ u then j s else 0) =
      (a + ∑ s ∈ insert k S, j s) + d * u := by
  sorry
