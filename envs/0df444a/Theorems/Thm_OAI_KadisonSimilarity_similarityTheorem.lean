-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_similarityTheorem
-- name    : OAI.KadisonSimilarity.similarityTheorem
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:49.942524+00:00
-- url     : https://prove2.me/theorems/8b750faf-2617-4cd7-a388-600466e9f0c2
-- statement:
--   The theorem states that, for every C*-algebra A in universe u and every complex inner product space K in universe v that is complete (a Hilbert space), every bounded unital representation of A on K is similar to a star representation. Here a bounded unital representation is a continuous ℂ-algebra homomorphism π from A into the algebra of bounded linear operators on K; being an algebra homomorphism of unital algebras, it preserves the identity. Similarity to a star representation means that there is an invertible bounded operator S on K, with bounded inverse, such that for every a in A, S π(a*) S⁻¹ equals the adjoint of S π(a) S⁻¹. Equivalently, the conjugated map a ↦ S π(a) S⁻¹ commutes with the involution. This is the Kadison similarity statement as a defined proposition SimilarityTheorem, and the source declares it as a theorem whose proof is admitted rather than supplied.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KadisonSimilarity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KadisonSimilarity.lean; bytes 4292..4437
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_KadisonSimilarity

namespace OAI

noncomputable section

namespace KadisonSimilarity

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Every bounded unital representation is similar to a star representation. -/
theorem similarityTheorem : SimilarityTheorem.{u,v} := by
  sorry

end KadisonSimilarity
end
end OAI
