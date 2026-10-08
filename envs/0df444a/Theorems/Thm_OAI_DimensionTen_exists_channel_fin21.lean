-- Prove2me | Theorems.Thm_OAI_DimensionTen_exists_channel_fin21
-- name    : OAI.DimensionTen.exists_channel_fin21
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:34.396288+00:00
-- url     : https://prove2.me/theorems/60d86307-c436-4820-942f-97755fed2ca9
-- statement:
--   The theorem states that there exists a linear map Θ from complex 21×21 matrices to complex 21×21 matrices (indexed by Fin 21) with three properties. First, Θ is PPT: it is completely positive, meaning that for every finite index type k, applying Θ to the second tensor factor of any positive semidefinite matrix on k × Fin 21 gives a positive semidefinite matrix, and the composition of the matrix transpose with Θ is also completely positive. Second, Θ is trace-preserving: tr Θ(X) = tr X for every matrix X. Third, the composition Θ∘Θ is not entanglement-breaking, where a map is entanglement-breaking if it is completely positive and, for every finite k and every positive semidefinite X on k × Fin 21, the amplified output is separable, meaning it equals a finite sum of Kronecker products A_i ⊗ B_i of positive semidefinite matrices. The statement is an admitted theorem in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DimensionTenChannel.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DimensionTenChannel.lean; bytes 1223..1564
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DimensionTenChannel

namespace OAI

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder

open Matrix

namespace DimensionTen

/-- A trace-preserving PPT channel on twenty-one dimensions with a non-entanglement-breaking square. -/
theorem exists_channel_fin21 :
    ∃ Θ : ChannelCompletion.Map (Fin 21) (Fin 21),
      ChannelCompletion.PPT Θ ∧ ChannelCompletion.TracePreserving Θ ∧
        ¬ ChannelCompletion.EntanglementBreaking (Θ.comp Θ) := by
  sorry

end DimensionTen
end
end OAI
