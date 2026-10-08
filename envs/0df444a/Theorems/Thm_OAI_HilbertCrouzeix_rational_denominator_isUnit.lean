-- Prove2me | Theorems.Thm_OAI_HilbertCrouzeix_rational_denominator_isUnit
-- name    : OAI.HilbertCrouzeix.rational_denominator_isUnit
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:45.239693+00:00
-- url     : https://prove2.me/theorems/abffe1ae-6d25-4672-b1d8-6894c40bf134
-- statement:
--   The theorem states that, for a nontrivial complete complex inner product space (Hilbert space) H, a bounded linear operator A on H, and an m×m matrix R of rational functions over ℂ (entries in RatFunc ℂ), the following holds. The numerical range of A is the set of values ⟨x, Ax⟩ over unit vectors x, and its numerical closure is the topological closure of that set. The pole-free set of R is the set of complex numbers z at which the denominator polynomial of every entry R_ij has nonzero value. If the numerical closure of A is contained in this pole-free set, then for every pair of indices i, j in Fin m, the operator obtained by substituting A into the denominator polynomial of R_ij is a unit, that is, an invertible element of the algebra of bounded operators on H.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HilbertCrouzeix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HilbertCrouzeix.lean; bytes 5674..5901
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_HilbertCrouzeix

namespace OAI

noncomputable section

open Complex Set

open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

theorem rational_denominator_isUnit [Nontrivial H] (A : H →L[ℂ] H)
    {m : ℕ} (R : RationalMatrix m) (hR : numericalClosure A ⊆ poleFreeSet R)
    (i j : Fin m) : IsUnit (Polynomial.aeval A (R i j).denom) := by
  sorry

end HilbertCrouzeix
end
end OAI
