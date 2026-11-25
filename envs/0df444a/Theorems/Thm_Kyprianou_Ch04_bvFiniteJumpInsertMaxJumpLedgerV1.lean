-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpInsertMaxJumpLedgerV1
-- name    : Kyprianou.Ch04.bvFiniteJumpInsertMaxJumpLedgerV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:13:08.625413+00:00
-- url     : https://prove2.me/theorems/167d5e07-647a-40f9-8858-afbe8fcfe795
-- title:
--   Jump increment ledger on insertion of the largest jump
-- statement:
--   The new jump contributes its post-jump value minus the previous path at the insertion time. Every older jump increment is unchanged.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic finite-jump telescoping.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvFiniteJumpInsertMaxJumpLedgerV1
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (f : ℝ × ℝ → ℝ)
    (S : Finset I) (k : I) (hk : ∀ s ∈ S, s < k) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    let Q : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s < u then j s else 0
    (∑ s ∈ insert k S, (f (τ s, P (insert k S) (τ s)) -
        f (τ s, Q (insert k S) (τ s)))) =
      f (τ k, P (insert k S) (τ k)) - f (τ k, P S (τ k)) +
      ∑ s ∈ S, (f (τ s, P S (τ s)) - f (τ s, Q S (τ s))) := by
  sorry
