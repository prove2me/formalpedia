-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzJumpLedgerV1
-- name    : Kyprianou.Ch04.exercise42LipschitzJumpLedgerV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:33:02.269411+00:00
-- url     : https://prove2.me/theorems/6a56821e-aa9d-5e18-b202-8428817a5a73
-- title:
--   Finite-jump insertion ledger for arbitrary first-coordinate path
-- statement:
--   Inserting a new last jump into a finite ordered jump set changes the two-coordinate jump ledger only at the last jump, for any first-coordinate function. This allows subsequent use of Lipschitz first-coordinate paths without altering the jump algebra.
-- source:
--   Supporting deterministic finite-jump calculus for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpInsertMaxJumpLedgerV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzJumpLedgerV1
    {I : Type} [LinearOrder I]
    (τ : I → ℝ) (hτ : StrictMono τ) (j : I → ℝ) (a d : ℝ)
    (U : ℝ → ℝ) (f : ℝ × ℝ → ℝ)
    (S : Finset I) (k : I) (hk : ∀ s ∈ S, s < k) :
    let P : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
    let Q : Finset I → ℝ → ℝ :=
      fun S u => a + d * u + ∑ s ∈ S, if τ s < u then j s else 0
    (∑ s ∈ insert k S, (f (U (τ s), P (insert k S) (τ s)) -
        f (U (τ s), Q (insert k S) (τ s)))) =
      f (U (τ k), P (insert k S) (τ k)) -
        f (U (τ k), P S (τ k)) +
      ∑ s ∈ S, (f (U (τ s), P S (τ s)) -
        f (U (τ s), Q S (τ s))) := by
  sorry
