-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpInsertMaxIntegralLedgerV1
-- name    : Kyprianou.Ch04.bvFiniteJumpInsertMaxIntegralLedgerV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:13:09.556157+00:00
-- url     : https://prove2.me/theorems/fb6610d2-6212-4529-bdd7-0b35a6c3b0ec
-- title:
--   Integral ledger on insertion of the largest jump
-- statement:
--   Split the time integral at the last jump. On the first interval the old path agrees almost everywhere. On the second the new path is affine, so the affine chain rule supplies the endpoint difference.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic finite-jump telescoping.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvFiniteJumpInsertMaxIntegralLedgerV1
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (S : Finset I) (k : I) (hk : ∀ s ∈ S, s < k)
    (T : ℝ) (hk0 : 0 < τ k) (hkT : τ k ≤ T) (hpos : ∀ s ∈ S, 0 < τ s) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    (∫ u in 0..T, fderiv ℝ f (u, P (insert k S) u) (1,d)) =
      (∫ u in 0..τ k, fderiv ℝ f (u, P S u) (1,d)) +
      (f (T, P (insert k S) T) - f (τ k, P (insert k S) (τ k))) := by
  sorry
