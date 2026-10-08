-- Prove2me | Theorems.Thm_OAI_NaimarkZFC_main
-- name    : OAI.NaimarkZFC.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:57.720575+00:00
-- url     : https://prove2.me/theorems/76ca3772-9b1a-4eba-9aae-47311f3a0da1
-- statement:
--   The theorem states that, for every universe level choice, there exists a type A carrying a C*-algebra structure (over ℂ) with the following five properties. First, A is simple in the sense that it is nontrivial and its only closed two-sided ideals are {0} and A itself. Second, A is not finite-dimensional as a complex vector space. Third, there is a continuous linear functional τ : A → ℂ that is a faithful tracial state: τ has norm 1, τ(a*a) is a nonnegative real number for every a, τ(ab) = τ(ba) for all a and b, and τ(a*a) > 0 whenever a ≠ 0. Fourth, A has a unique irreducible representation up to unitary equivalence: whenever π and ρ are nonzero star-homomorphisms (non-unital algebra homomorphisms preserving star) from A into the bounded operators on complete complex inner product spaces H and K, taken in the stated universe levels, and each has no closed invariant subspace other than 0 and the whole space, there is a linear isometric isomorphism U : H → K with U(π(a)x) = ρ(a)(Ux) for all a and x. Fifth, for every complete complex inner product space H in the stated universe, A is not isomorphic to the algebra of compact operators on H, meaning there is no injective star-homomorphism φ : A → B(H) whose range is exactly the set of compact operators on H.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Naimark.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Naimark.lean; bytes 2029..2407
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_Naimark

namespace OAI

noncomputable section

universe u v w

namespace NaimarkZFC

theorem main :
    ∃ (A : Type u) (_ : CStarAlgebra A),
      IsSimpleCStar A ∧ ¬ FiniteDimensional ℂ A ∧
      (∃ τ : A →L[ℂ] ℂ, IsFaithfulTracialState τ) ∧
      HasUniqueIrreducibleRepresentation.{u, v, w} A ∧
      ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
        ¬ IsIsomorphicToCompacts A H := by
  sorry

end NaimarkZFC
end
end OAI
