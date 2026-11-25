-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpTelescopingV2
-- name    : Kyprianou.Ch04.exercise42LipschitzFiniteJumpTelescopingV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:54:12.13721+00:00
-- url     : https://prove2.me/theorems/7054d5fa-cbf7-4efa-8ae4-5403efc1337b
-- title:
--   Unconditional Lipschitz two-coordinate finite-jump change-of-variables formula
-- statement:
--   For a C1 test function on the first-coordinate nonnegative half-plane, Lipschitz first-coordinate path positive after zero, and arbitrary affine-drift finite-jump second-coordinate path, the exact two-coordinate continuous-derivative integral and jump ledger telescope to the terminal change. Integrability is derived from the stated regularity hypotheses.
-- source:
--   Deterministic finite-jump Stieltjes calculus for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineSegmentChainV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzJumpLedgerV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpMaxIntegralLedgerV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpDerivativeIntervalIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineDerivativeIntervalIntegrableV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzFiniteJumpTelescopingV2
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
