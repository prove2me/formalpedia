-- Prove2me | Theorems.Thm_MultiIndex_alternating_binomial_convolution
-- name    : MultiIndex.alternating_binomial_convolution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T14:34:17.881251+00:00
-- url     : https://prove2.me/theorems/c9dcfeee-0cf3-4628-a22c-aa5b51e97c81
-- title:
--   Alternating multi-index binomial convolution cancellation
-- statement:
--   Let the coordinate type be finite, R a commutative ring, α a natural-valued multi-index, and S a finite set containing every coordinatewise sub-index of α. For an arbitrary R-valued two-index array F, summing the nested binomial expression in the formal statement leaves only (−1)^|α| F(0,α). All subtractions are coordinatewise truncated natural subtraction. Extra indices in S contribute zero: nonzero coefficients require γ≤β≤α. On that down-set the first argument of F becomes α−γ, and the identity follows by the binomial coefficient product formula and coordinatewise alternating binomial cancellation. This theorem is purely algebraic and does not assume any calculus structure.
-- source:
--   Derived multi-index binomial inversion identity. Elementary ingredients in the pinned Mathlib are Nat.choose_mul (Mathlib/Data/Nat/Choose/Basic.lean) and Int.alternating_sum_range_choose (Mathlib/Data/Nat/Choose/Sum.lean), https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Choose. The multi-index convolution statement is a derived algebraic lemma, not quoted as a theorem from Hunter.

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic

theorem MultiIndex.alternating_binomial_convolution
    {ι R : Type*} [Fintype ι] [CommRing R]
    (α : ι → ℕ) (s : Finset (ι → ℕ))
    (hs : ∀ β : ι → ℕ, (∀ i, β i ≤ α i) → β ∈ s)
    (F : (ι → ℕ) → (ι → ℕ) → R) :
    (∑ β ∈ s, (∏ i, (Nat.choose (α i) (β i) : R)) *
      (-1 : R) ^ (∑ i, β i) *
      (∑ γ ∈ s, (∏ i, (Nat.choose (β i) (γ i) : R)) *
        F (fun i => α i - β i + (β i - γ i)) γ)) =
      (-1 : R) ^ (∑ i, α i) * F (fun _ => 0) α := by sorry
