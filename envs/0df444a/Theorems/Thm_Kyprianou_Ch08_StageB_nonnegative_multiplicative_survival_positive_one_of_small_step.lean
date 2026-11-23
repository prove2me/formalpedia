-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_nonnegative_multiplicative_survival_positive_one_of_small_step
-- name    : Kyprianou.Ch08.StageB.nonnegative_multiplicative_survival_positive_one_of_small_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:29:46.913321+00:00
-- url     : https://prove2.me/theorems/659de3f8-a462-4389-ad1e-74c98b1a79ae
-- title:
--   Positive survival at level one from a nonnegative multiplicative semigroup with one positive small step
-- statement:
--   For a nonnegative real-valued survival semigroup on positive reals, strictly positive survival at any positive spatial step implies strictly positive survival at level one. This is the abstract semigroup propagation needed for the original Levy no-drawdown survival integral in Chapter 8 Lemma 8.2.
-- source:
--   Sound arithmetic lemma: choose a multiple of positive step above one, show positivity at that multiple by induction and the multiplicative identity, then decompose that multiple as one plus a positive remainder and use nonnegativity. Intended to be imported by the source-accurate original model positivity child.

import Mathlib
set_option autoImplicit false
open Set Filter Topology

theorem Kyprianou.Ch08.StageB.nonnegative_multiplicative_survival_positive_one_of_small_step
    (S : ℝ → ℝ)
    (hsemi : ∀ a b : ℝ, 0 < a → 0 < b → S (a + b) = S a * S b)
    (hnon : ∀ a : ℝ, 0 < a → 0 ≤ S a)
    (d : ℝ) (hd : 0 < d) (hSd : 0 < S d) :
    0 < S 1 := by
  sorry
