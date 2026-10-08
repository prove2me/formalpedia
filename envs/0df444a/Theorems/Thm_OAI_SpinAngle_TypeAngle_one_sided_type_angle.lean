-- Prove2me | Theorems.Thm_OAI_SpinAngle_TypeAngle_one_sided_type_angle
-- name    : OAI.SpinAngle.TypeAngle.one_sided_type_angle
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:25.204808+00:00
-- url     : https://prove2.me/theorems/77f915ff-80da-462a-85e9-2f236c09776f
-- statement:
--   The theorem states the following for a positive integer q, finite row and column index types R and C, and a finite set W of cells in R × C. A type label of order q is a pair of Young diagrams (an even one and an odd one), each with first-column length at most q; its size is the total number of cells of the two diagrams, its entropy is N log N − Σ nᵢ log nᵢ for the vector of all 2q row lengths (N being their sum), its dimension is the complex dimension of the tensor product of the two associated polynomial-representation carriers, and its projection is the orthogonal projection onto the corresponding isotypic component of the unitary-group representation on the tensor space over the signed spin alphabet Fin q × Bool. Let D be a type label with size |W|, regarded through the projection D.projection W on the space indexed by W. Let H assign a type label to each column j, whose size equals the number of cells of W in column j, and K assign a type label to each row i, whose size equals the number of cells of W in row i. Write P_H for the block-tensor product, over columns, of the projections of the labels H(j) on the fibers of the column map, P_K for the analogous product over rows, entropy(H) and entropy(K) for the sums of the label entropies, and dim(H), dim(K) for the products of the label dimensions. Let φ(W) be the product over rows i of the factor (|C|/o_i)^{o_i}, where o_i is the number of cells of W in row i, taken as 1 for a row with all |C| cells occupied. Then, with the operator norm, three claims hold. First, ‖P_H P_K D.projection W‖² ≤ min(1, exp(entropy(H) + entropy(K) − entropy(D)) · dim(H) · dim(K) · φ(W)). Second, that minimum is at most min(1, exp(entropy(H) + entropy(K) − entropy(D) + (|R||C| − |W|)) · dim(H) · dim(K)). Third, dim(H) · dim(K) ≤ (|W| + 1)^{(|R| + |C|) q (q − 1)}. The proof is admitted with sorry in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SpinAngle.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SpinAngle.lean; bytes 17945..19042
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SpinAngle

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Matrix TensorProduct

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace SpinAngle.TypeAngle

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {q : ℕ} [Nonempty (Fin q)]

variable {R C : Type*}

variable [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

theorem one_sided_type_angle (W : Finset (R × C))
    (D : TypeLabel q) (H : C → TypeLabel q) (K : R → TypeLabel q)
    (hD : D.size = W.card)
    (hH : ∀ j, (H j).size = Fintype.card (TypeBlocks.Fiber (column W) j))
    (hK : ∀ i, (K i).size = Fintype.card (TypeBlocks.Fiber (row W) i)) :
    (‖TypeBlocks.projection (column W) H * TypeBlocks.projection (row W) K * D.projection W‖ ^ 2 ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W)) ∧
    (min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W) ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy +
        (Fintype.card R * Fintype.card C - W.card : ℕ)) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ))) ∧
    TypeBlocks.dimension H * TypeBlocks.dimension K ≤
      (W.card + 1) ^ ((Fintype.card R + Fintype.card C) * q * (q - 1)) := by
  sorry

end SpinAngle.TypeAngle
end
end OAI
