-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_affine_unit_propagation_zero
-- name    : NestedSeatAlloc.IntPolicy.clbi_affine_unit_propagation_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T09:03:39.385627+00:00
-- url     : https://prove2.me/theorems/6e461cfa-7fd9-47ad-b3fb-088f007b6da8
-- title:
--   Sign-free base case for affine CLBI propagation
-- statement:
--   For integer-valued nonnegative demand, the expected single-class truncated-revenue function is affine on each closed unit interval, without assuming the fare is nonnegative or the demand has finite mean.
-- source:
--   The k=0 case of NestedSeatAlloc.IntPolicy.clbi_affine_unit_propagation. At level 1, revenue is f 1 * min s (X 1); integer-valued nonnegative demand splits each closed unit interval into a bounded constant branch and a bounded affine branch. The expected-affine identity holds for either sign of f 1 and does not require E[X 1] to be finite.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem clbi_affine_unit_propagation_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (p : ℕ → ℕ) :
    ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) 1 s = a + b * s := by sorry

end NestedSeatAlloc.IntPolicy
