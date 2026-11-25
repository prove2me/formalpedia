-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpTelescopingV1
-- name    : Kyprianou.Ch04.exercise42LipschitzFiniteJumpTelescopingV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:41:32.26539+00:00
-- url     : https://prove2.me/theorems/427b3fb5-8c36-4ece-93b5-27ce89e3a301
-- title:
--   Two-coordinate finite-jump chain rule with Lipschitz first coordinate
-- statement:
--   The finite-jump telescoping change-of-variables identity for an affine-drift plus finite-jump path under a Lipschitz nonnegative first coordinate, assuming the natural finite-jump and affine segment integrability conditions.
-- source:
--   Deterministic finite-jump Stieltjes calculus for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineSegmentChainV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzJumpLedgerV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpMaxIntegralLedgerV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzFiniteJumpTelescopingV1
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (U : ℝ → ℝ) (K : ℝ≥0) (hULip : LipschitzWith K U)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ)) :
    let P : Finset I → ℝ → ℝ :=
      fun R u => a + d * u + ∑ s ∈ R, if τ s ≤ u then j s else 0
    let Q : Finset I → ℝ → ℝ :=
      fun R u => a + d * u + ∑ s ∈ R, if τ s < u then j s else 0
    let D : Finset I → ℝ → ℝ :=
      fun R u => fderiv ℝ f (U u, P R u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, P R u) (0, 1)
    (∀ (R : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s) →
      (∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) →
      IntervalIntegrable (D R) volume 0 T) →
    (∀ (b l r : ℝ), 0 ≤ l → l ≤ r →
      (∀ s ∈ Icc l r, 0 ≤ U s) →
      (∀ s ∈ Ioc l r, 0 < U s) →
      IntervalIntegrable (fun u =>
        fderiv ℝ f (U u, b + d * u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, b + d * u) (0, 1)) volume l r) →
    ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) →
      (∀ s ∈ S, τ s ≤ T) →
      (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s) →
      (∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) →
      f (U T, P S T) = f (U 0, a) +
        (∫ u in 0..T, D S u) +
        ∑ s ∈ S, (f (U (τ s), P S (τ s)) -
          f (U (τ s), Q S (τ s))) := by
  sorry
