-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpMaxIntegralLedgerV1
-- name    : Kyprianou.Ch04.exercise42LipschitzFiniteJumpMaxIntegralLedgerV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:36:01.412028+00:00
-- url     : https://prove2.me/theorems/fb6a409f-6438-42e3-b0ea-9d0810708c5a
-- title:
--   Last-jump continuous-integral ledger for Lipschitz first coordinate
-- statement:
--   For a finite-jump affine-drift path, adding its greatest jump time splits the two-coordinate continuous integral into the pre-jump integral and the affine post-jump change of f along the same Lipschitz first coordinate, assuming the two displayed continuous integrands are interval-integrable.
-- source:
--   Deterministic finite-jump Stieltjes calculus for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpAfterMaxAffineV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineSegmentChainV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzFiniteJumpMaxIntegralLedgerV1
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (U : ℝ → ℝ) (K : ℝ≥0) (hULip : LipschitzWith K U)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (S : Finset I) (k : I) (hk : ∀ s ∈ S, s < k)
    (T : ℝ) (hk0 : 0 < τ k) (hkT : τ k ≤ T)
    (hNonneg : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ U s)
    (hPositive : ∀ s ∈ Ioc (0 : ℝ) T, 0 < U s) :
    let P : Finset I → ℝ → ℝ :=
      fun R u => a + d * u + ∑ s ∈ R, if τ s ≤ u then j s else 0
    let D : Finset I → ℝ → ℝ :=
      fun R u => fderiv ℝ f (U u, P R u) (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, P R u) (0, 1)
    IntervalIntegrable (D S) volume 0 (τ k) →
    IntervalIntegrable (fun u =>
      fderiv ℝ f (U u, (a + ∑ s ∈ insert k S, j s) + d * u)
        (1, 0) * deriv U u +
        d * fderiv ℝ f (U u, (a + ∑ s ∈ insert k S, j s) + d * u)
          (0, 1)) volume (τ k) T →
    (∫ u in 0..T, D (insert k S) u) =
      (∫ u in 0..τ k, D S u) +
      (f (U T, P (insert k S) T) -
        f (U (τ k), P (insert k S) (τ k))) := by
  sorry
