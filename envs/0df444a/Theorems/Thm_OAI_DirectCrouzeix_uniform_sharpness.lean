-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_uniform_sharpness
-- name    : OAI.DirectCrouzeix.uniform_sharpness
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:34.792656+00:00
-- url     : https://prove2.me/theorems/0c1828de-65ff-47b7-b09e-e30fdec206f9
-- statement:
--   The theorem states that any real constant c that is a universal bound in the following sense must satisfy 2 ≤ c. UniversalBound(c) is the defined proposition that for all natural numbers n, m, d with n>0 and m>0, every complex n×n matrix A, and every family of d+1 complex m×m matrices B₀, …, B_d, the operator (L2 spectral) norm of the tensor evaluation Σₖ Aᵏ ⊗ Bₖ, a Kronecker-product matrix of size nm×nm, is at most c times the range maximum. The range maximum is the supremum, over z in the numerical range of A, of the operator norm of the matrix polynomial Σₖ zᵏ Bₖ. The numerical range of A is the set of all values ⟨u, A u⟩ over unit vectors u in complex Euclidean space ℂⁿ. The result is stated with a sorry placeholder, so no proof is claimed here, and it says that the constant 2 cannot be lowered.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectCrouzeix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DirectCrouzeix.lean; bytes 1235..1318
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DirectCrouzeix

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

theorem uniform_sharpness (c : ℝ) (hc : UniversalBound c) : 2 ≤ c := by
  sorry

end DirectCrouzeix
end
end OAI
