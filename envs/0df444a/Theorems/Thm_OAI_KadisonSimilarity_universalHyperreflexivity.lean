-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_universalHyperreflexivity
-- name    : OAI.KadisonSimilarity.universalHyperreflexivity
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:50.278985+00:00
-- url     : https://prove2.me/theorems/3bf47a5f-7f89-422d-a1df-9b0f5dc5ecfb
-- statement:
--   The theorem states that the explicit absolute constant universalConstant makes the universal hyperreflexivity property hold, for Hilbert spaces in the fixed universe u. Here universalConstant = 3·factorConstant + 2, where factorConstant = max(3·cornerConstant + 2, 1 + 2·rowConstant, 2), cornerConstant = 6π²(1 + 4·cyclicConstant), cyclicConstant = (1 + 4·rowConstant)², and rowConstant = 4√2. The property UniversalHyperreflexivity(C) says that for every complex Hilbert space K in that universe, every von Neumann algebra M of operators on K, and every bounded operator T on K, the operator-norm distance from T to the set M is at most 2·C·offDiagonalSeminorm(M,T). The off-diagonal seminorm is the supremum, over all projections e in the commutant of M (self-adjoint idempotent bounded operators commuting with M), of the norm ‖(1 − e) T e‖. So the theorem gives, with C = universalConstant, dist(T, M) ≤ 2·universalConstant·sup_e ‖(1 − e) T e‖ for all such K, M and T.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KadisonSimilarity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KadisonSimilarity.lean; bytes 4097..4290
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_KadisonSimilarity

namespace OAI

noncomputable section

namespace KadisonSimilarity

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Every von Neumann algebra has hyperreflexivity constant at most `2 * universalConstant`. -/
theorem universalHyperreflexivity : UniversalHyperreflexivity.{u} universalConstant := by
  sorry

end KadisonSimilarity
end
end OAI
