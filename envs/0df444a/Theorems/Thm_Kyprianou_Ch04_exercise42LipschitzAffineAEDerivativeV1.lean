-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineAEDerivativeV1
-- name    : Kyprianou.Ch04.exercise42LipschitzAffineAEDerivativeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:25:38.858486+00:00
-- url     : https://prove2.me/theorems/52b52bfe-0c43-4840-94b6-72bb4bd7a12f
-- title:
--   Almost-everywhere derivative of a C1 affine/Lipschitz composition
-- statement:
--   At almost every interior time where the Lipschitz coordinate is differentiable and positive, the derivative of the two-coordinate composition is the sum of its partial-coordinate derivatives.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.2, printed page 106.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzAffineAEDerivativeV1
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ)
    (hPositive : ∀ s ∈ Ioc l r, 0 < U s) :
    ∀ᵐ s ∂volume, s ∈ Ioc l r →
      deriv (fun u : ℝ => f (U u, a + c * u)) s =
        fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
          c * fderiv ℝ f (U s, a + c * s) (0, 1) := by
  sorry
