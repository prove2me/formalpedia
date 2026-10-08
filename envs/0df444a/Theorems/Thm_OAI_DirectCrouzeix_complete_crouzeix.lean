-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_complete_crouzeix
-- name    : OAI.DirectCrouzeix.complete_crouzeix
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:34.662313+00:00
-- url     : https://prove2.me/theorems/bed33a2b-dd21-4a3b-9f7d-472ccb587aad
-- statement:
--   The theorem states (admitted without proof in the source) that the defined proposition UniversalBound holds with constant c = 2. Unfolded: for all natural numbers n, m, d with n>0 and m>0, every complex n×n matrix A, and every family B₀,…,B_d of complex m×m matrices, the operator norm (L2 operator norm) of the tensor evaluation Σₖ Aᵏ ⊗ Bₖ (a Kronecker product, an nm×nm matrix, with k from 0 to d) is at most 2 times the range maximum. The range maximum is the supremum, over z in the numerical range of A, of the operator norm of the matrix polynomial value Σₖ zᵏ Bₖ. The numerical range of A is the set of all inner products ⟨u, Au⟩ with u a unit vector in ℂⁿ (Euclidean norm 1). This is a matrix-coefficient, vector-valued form of the Crouzeix bound with constant 2.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectCrouzeix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DirectCrouzeix.lean; bytes 1175..1233
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DirectCrouzeix

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

theorem complete_crouzeix : UniversalBound 2 := by
  sorry

end DirectCrouzeix
end
end OAI
