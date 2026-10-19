-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_mul_norm_le_sum_bound
-- name    : OAI.PiExponent.LiteralAnalytic.coeff_mul_norm_le_sum_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:01:52.027992+00:00
-- url     : https://prove2.me/theorems/66d18eb1-31bc-4133-821c-6ce161772e7c
-- title:
--   Power series coefficient convolution norm bound
-- statement:
--   If one power series has coefficient norms bounded termwise by a real sequence and the other has coefficient norms bounded by a nonnegative constant, then the norm of the nth product coefficient is bounded by that constant times the sum of the first n+1 sequence bounds.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.coeff_mul_norm_le_sum_bound
    (f g : PowerSeries ℂ) (a : ℕ → ℝ) (B : ℝ) (n : ℕ)
    (hB : 0 ≤ B)
    (hf : ∀ r, ‖PowerSeries.coeff r f‖ ≤ a r)
    (hg : ∀ r, ‖PowerSeries.coeff r g‖ ≤ B) :
    ‖PowerSeries.coeff n (f * g)‖ ≤
      B * ∑ r ∈ Finset.range (n + 1), a r := by sorry
