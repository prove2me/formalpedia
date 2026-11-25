-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpFderivIntegrableV1
-- name    : Kyprianou.Ch04.exercise42LipschitzFiniteJumpFderivIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:03:07.708284+00:00
-- url     : https://prove2.me/theorems/04ead8ba-f25e-4358-a1f4-c2ed209dd215
-- title:
--   Componentwise interval integrability along Lipschitz finite-jump paths
-- statement:
--   Each fixed directional derivative of a C1On test function, evaluated along a positive Lipschitz first coordinate and finite-jump affine-drift second coordinate, is integrable on compact intervals.
-- source:
--   Deterministic BV Stieltjes calculus for Kyprianou (2006), Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineFderivIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpAfterMaxAffineV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzFiniteJumpFderivIntegrableV1
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (U : ℝ → ℝ) (K : ℝ≥0) (hULip : LipschitzWith K U)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (v : ℝ × ℝ) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
      (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s) →
      (∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) →
      IntervalIntegrable (fun u =>
        fderiv ℝ f (U u, P S u) v) volume 0 T := by
  sorry
