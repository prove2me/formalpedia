-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpDerivativeIntervalIntegrableV1
-- name    : Kyprianou.Ch04.exercise42LipschitzFiniteJumpDerivativeIntervalIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:47:23.99684+00:00
-- url     : https://prove2.me/theorems/a363b9bc-462b-571a-9f54-b085b606458b
-- title:
--   Derivative integrability for finite-jump BV path with Lipschitz first coordinate
-- statement:
--   For a C1 test function on the nonnegative first-coordinate half-plane, a Lipschitz first-coordinate path positive on positive times, and a finite-jump affine-drift second-coordinate path, the two-coordinate chain-rule derivative integrand is interval-integrable.
-- source:
--   Deterministic Stieltjes calculus for Kyprianou (2006), Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineDerivativeIntervalIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpAfterMaxAffineV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzFiniteJumpDerivativeIntervalIntegrableV1
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (U : ℝ → ℝ) (K : ℝ≥0) (hULip : LipschitzWith K U)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ)) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
      (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s) →
      (∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) →
      IntervalIntegrable (fun u =>
        fderiv ℝ f (U u, P S u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, P S u) (0, 1)) volume 0 T := by
  sorry
