-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_main_no_embedding
-- name    : OAI.NuclearUltrapower.main_no_embedding
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:58.081347+00:00
-- url     : https://prove2.me/theorems/6078f168-02cc-4caa-ab45-afb85fc2a2be
-- statement:
--   The theorem states that, working in universe level 0, there exist a nonzero unital complex C*-algebra A and a group homomorphism ι from G into the unitary group of A such that the following hold. Here G is the semidirect product of the additive group of 3-vectors over the dyadic rationals Z[1/2] by SL₃(ℤ) × ℤ, where a matrix acts linearly on the vectors and the integer n acts by multiplication by 2ⁿ. First, (A, ι) is the full group C*-algebra of G: the span of ι(G) is dense in A, and every homomorphism of G into the unitaries of a nonzero unital C*-algebra D extends uniquely to a unital *-homomorphism A → D. Second, A is separable as a topological space. Third, for every nonzero unital C*-algebra B that is nuclear in the tensor-norm sense (minimal and maximal C*-tensor norms agree on B ⊗ C for every C*-algebra C) and every free ultrafilter ω on ℕ (one containing no finite set), there is no injective unital *-homomorphism from A into the norm ultrapower of B, namely bounded B-valued sequences modulo those tending to 0 along ω. Fourth, there exist a nonzero unital C*-algebra O and two elements s₀, s₁ of O satisfying the Cuntz relations (each sᵢ*sᵢ = 1 and s₀s₀* + s₁s₁* = 1), with O universal for these relations, such that for every free ultrafilter ω there is likewise no injective unital *-homomorphism from A into the norm ultrapower of O. The theorem is admitted in the source, not proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/NuclearUltrapower.lean; bytes 9109..9343
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_NuclearUltrapower

namespace OAI

namespace NuclearUltrapower

/-- The full dyadic group C*-algebra has no nuclear norm-ultrapower embedding,
including the corollary for the universal Cuntz algebra on two isometries. -/
theorem main_no_embedding : MainStatementWithCuntzCorollary.{0} := by
  sorry

end NuclearUltrapower
end OAI
