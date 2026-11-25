-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineDerivativeIntervalIntegrableV1
-- name    : Kyprianou.Ch04.exercise42LipschitzAffineDerivativeIntervalIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:44:45.435577+00:00
-- url     : https://prove2.me/theorems/897d740e-e99a-5ccd-a25e-34a225007729
-- title:
--   Integrability of the Lipschitz-affine two-coordinate chain-rule derivative
-- statement:
--   For a Lipschitz nonnegative first coordinate and an affine second coordinate, the chain-rule derivative integrand is interval-integrable along any compact segment where the first coordinate is positive in its interior.
-- source:
--   Deterministic Stieltjes calculus for Kyprianou (2006), Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineACV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineAEDerivativeV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzAffineDerivativeIntervalIntegrableV1
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ) (hlr : l ≤ r)
    (hNonneg : ∀ s ∈ Icc l r, 0 ≤ U s)
    (hPositive : ∀ s ∈ Ioc l r, 0 < U s) :
    IntervalIntegrable
      (fun s : ℝ => fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
        c * fderiv ℝ f (U s, a + c * s) (0, 1)) volume l r := by
  sorry
