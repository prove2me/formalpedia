-- Prove2me | Theorems.Thm_OAI_CompleteCrouzeix_main
-- name    : OAI.CompleteCrouzeix.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:27.931484+00:00
-- url     : https://prove2.me/theorems/ac54c442-d537-44ab-9a2e-0bafc36130f1
-- statement:
--   The theorem states two things about the defined proposition UniversalBound(C), which is a statement about a real constant C. UniversalBound(C) says that for all natural numbers n, m, d with n>0 and m>0, every complex n×n matrix A and every family B₀,…,B_d of complex m×m matrices satisfy ‖Σₖ Aᵏ ⊗ Bₖ‖ ≤ C · M, where the Kronecker products Aᵏ ⊗ Bₖ are summed to form a matrix of size nm×nm, the norm is the matrix operator norm for the Euclidean (L2) structure, and M is the supremum of ‖Σₖ zᵏBₖ‖ over z in the numerical range of A. The numerical range of A is the set of values ⟨x, Ax⟩ over unit vectors x in ℂⁿ. The first conclusion is that UniversalBound holds with C = 2. The second is that any real C for which UniversalBound(C) holds must satisfy C ≥ 2, so 2 is the smallest possible universal constant. The proof is admitted in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CompleteCrouzeix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CompleteCrouzeix.lean; bytes 1189..1280
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CompleteCrouzeix

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace CompleteCrouzeix

theorem main : UniversalBound 2 ∧ ∀ C : ℝ, UniversalBound C → 2 ≤ C := by
  sorry

end CompleteCrouzeix
end
end OAI
