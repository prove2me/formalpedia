-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpDerivativeIntervalIntegrableV1
-- name    : Kyprianou.Ch04.bvFiniteJumpDerivativeIntervalIntegrableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:04:32.493817+00:00
-- url     : https://prove2.me/theorems/0aedac48-a3c1-4821-b537-f0ce03a4f48d
-- title:
--   Derivative interval integrability on a finite-jump affine path
-- statement:
--   Induct by the largest retained jump time. Before it the new path equals the previous finite path, and after it the path is affine with all retained jumps included. Endpoint exceptions are null. Glue interval integrability on the two intervals.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic finite-jump telescoping.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvFiniteJumpDerivativeIntervalIntegrableV1
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ)) (v : ℝ × ℝ) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    ∀ (S : Finset I) (T : ℝ), 0 ≤ T →
      (∀ s ∈ S, 0 < τ s) → (∀ s ∈ S, τ s ≤ T) →
      IntervalIntegrable (fun u => fderiv ℝ f (u, P S u) v) volume 0 T := by
  sorry
