-- Prove2me | Theorems.Thm_Kyprianou_Ch04_affineGridLedgerVariationBoundV1
-- name    : Kyprianou.Ch04.affineGridLedgerVariationBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:43:18.210251+00:00
-- url     : https://prove2.me/theorems/264f669d-a5da-5129-8e5a-7f37c4088856
-- title:
--   affineGridLedgerVariationBoundV1
-- statement:
--   Variation bound from individual affine ledger component budgets.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_positive_monotone_grid_variation
open MeasureTheory Set
open scoped NNReal Classical
set_option autoImplicit false

/-- Summing the absolute increments of an affine path ledger is bounded
by the sum of the absolute variation budgets of its constituents. -/
theorem Kyprianou.Ch04.affineGridLedgerVariationBoundV1 (S : Finset NNReal) (a : NNReal → ℝ) (b T : ℝ)
    (n : ℕ) (v y : ℕ → ℝ) (J : NNReal → ℕ → ℝ)
    (he : ∀ k, y (k+1)-y k = b*(v (k+1)-v k) +
      ∑ r ∈ S,a r*(J r (k+1)-J r k))
    (hV : (∑ k ∈ Finset.range n, |v (k+1)-v k|) ≤ T)
    (hJ' : ∀ r, (∑ k ∈ Finset.range n, |J r (k+1)-J r k|) ≤ 1) :
    (∑ k ∈ Finset.range n, |y (k+1)-y k|) ≤ |b| * T+∑ r ∈ S,|a r| := by
  sorry
