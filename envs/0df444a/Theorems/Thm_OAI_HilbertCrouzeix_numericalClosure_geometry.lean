-- Prove2me | Theorems.Thm_OAI_HilbertCrouzeix_numericalClosure_geometry
-- name    : OAI.HilbertCrouzeix.numericalClosure_geometry
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:45.08499+00:00
-- url     : https://prove2.me/theorems/6702b653-335f-479b-8181-0973a6ac7ba9
-- statement:
--   The theorem states that for every bounded complex-linear operator A on a complex Hilbert space H (a complete complex inner product space), the numerical closure of A has three properties. Here the numerical range of A is the set of complex numbers ⟨x, Ax⟩ over unit vectors x in H, and the numerical closure is the topological closure of that set in ℂ. The conclusion is that this closure is compact, that it is convex as a subset of ℂ viewed as a real vector space, and that it contains the spectrum of A, meaning every λ for which A − λ is not invertible lies in the closure.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HilbertCrouzeix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HilbertCrouzeix.lean; bytes 4999..5187
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

theorem numericalClosure_geometry (A : H →L[ℂ] H) :
    IsCompact (numericalClosure A) ∧ Convex ℝ (numericalClosure A) ∧
      spectrum ℂ A ⊆ numericalClosure A := by
  sorry

end HilbertCrouzeix
end
end OAI
