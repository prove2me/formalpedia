-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_character_criterion
-- name    : OAI.KirchbergRordam.character_criterion
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:51.69307+00:00
-- url     : https://prove2.me/theorems/33f0d9e9-3a44-4567-b9fa-80118317431f
-- statement:
--   The theorem states that, for a nontrivial separable C*-algebra A (in the base universe Type) and a free ultrafilter ω on the natural numbers, meaning an ultrafilter that refines the cofinite filter, the norm central-sequence algebra of A has no characters if and only if A is isomorphic to its minimal (spatial) C*-tensor product with the Jiang–Su algebra. The norm ultrapower of A is the quotient of the C*-algebra of bounded sequences in A by the ideal of sequences whose norms tend to zero along ω; the central algebra is the closed star-subalgebra of this ultrapower consisting of elements commuting with the diagonal copy of A, the images of constant sequences. The central algebra has no characters means that every star-homomorphism from it to ℂ (a linear, multiplicative, star-preserving map, not required to preserve the unit) is the zero map. The Jiang–Su algebra is the inductive limit C*-algebra of the standard prime-dimension-drop model system. The right-hand side asserts the existence of a star-algebra isomorphism over ℂ from A onto this tensor product. The proof is admitted in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CharacterCriterion.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CharacterCriterion.lean; bytes 135077..135423
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CharacterCriterion

namespace OAI

noncomputable section

open scoped TensorProduct CStarAlgebra InnerProductSpace Matrix Kronecker ComplexOrder

open UniformSpace Filter Topology BoundedContinuousFunction

universe uQuot

namespace KirchbergRordam

theorem character_criterion
    (A : Type) [CStarAlgebra A] [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.cofinite) :
    OAI.KirchbergRordam.HasNoCharacters (NormUltrapower.CentralAlgebra A ω) ↔
      Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A JiangSu.Algebra) := by sorry

end KirchbergRordam
end
end OAI
