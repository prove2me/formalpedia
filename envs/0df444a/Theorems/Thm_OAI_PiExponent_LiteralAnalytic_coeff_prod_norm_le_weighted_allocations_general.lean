-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_prod_norm_le_weighted_allocations_general
-- name    : OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_allocations_general
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:28:27.737986+00:00
-- url     : https://prove2.me/theorems/34330063-bd39-4d7d-bd76-68c3223c0fdd
-- title:
--   Product coefficient bound from nonnegative coefficient majorants
-- statement:
--   For a finite family of complex power series, if every coefficient norm is bounded by a nonnegative real majorant, then the norm of the degree-k coefficient of the product is bounded by the sum of products of those majorants over all degree allocations totaling k.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_allocations_general
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → PowerSeries ℂ) (B : σ → ℕ → ℝ) (k : ℕ)
    (hB : ∀ i n, 0 ≤ B i n)
    (hf : ∀ i n, ‖PowerSeries.coeff n (f i)‖ ≤ B i n) :
    ‖PowerSeries.coeff k (∏ i, f i)‖ ≤
      ∑ n : σ → Fin (k + 1),
        (if ∑ i, (n i : ℕ) = k then ∏ i, B i (n i : ℕ) else 0) := by
  sorry
