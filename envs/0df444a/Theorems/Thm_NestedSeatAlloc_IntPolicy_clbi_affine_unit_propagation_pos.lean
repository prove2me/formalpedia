-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_affine_unit_propagation_pos
-- name    : NestedSeatAlloc.IntPolicy.clbi_affine_unit_propagation_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T09:02:04.763977+00:00
-- url     : https://prove2.me/theorems/8e1ee4c8-6861-40fa-8d3b-46e943c721f1
-- title:
--   Positive-index step of affine CLBI propagation
-- statement:
--   For a positive current fare-class index k, if expected revenue through k is affine on every closed unit interval, then expected revenue through k+1 is also affine on every closed unit interval.
-- source:
--   Source-faithful positive-index case of NestedSeatAlloc.IntPolicy.clbi_affine_unit_propagation. It isolates the non-base induction step: conditioning on the next integer-valued demand, using prefix independence to factor each atom/tail payoff, and combining shifted unit-affine pieces. The parent handles k=0 separately via the sign-free integer-min truncation identity.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem clbi_affine_unit_propagation_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (k : ℕ) (hk : 0 < k) (p : ℕ → ℕ)
    (hunit : ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) k s = a + b * s) :
    ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) (k + 1) s = a + b * s := by sorry

end NestedSeatAlloc.IntPolicy
