-- Prove2me | Theorems.Thm_OAI_HilbertCrouzeix_exists_finite_compression
-- name    : OAI.HilbertCrouzeix.exists_finite_compression
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:44.937693+00:00
-- url     : https://prove2.me/theorems/db6ac979-f844-4765-9969-054291c0437c
-- statement:
--   The theorem states that, for any complex Hilbert-space operator setting with H an inner product space over ℂ (completeness is not needed), natural numbers m and d, a bounded linear operator A on H, a family B₀,…,B_d of m×m complex matrices, and a vector ξ in the algebraic tensor product H ⊗ ℂ^m (viewed inside the completed amplification of H by ℂ^m, the Hilbert-space completion of that tensor product), there is a finite-dimensional complex subspace E of H and a vector η in the corresponding amplification of E by ℂ^m satisfying two conditions. First, the isometric inclusion of the amplification of E into that of H, induced by the inclusion E ⊆ H and the identity on ℂ^m, sends η to ξ. Second, applying the matrix-coefficient polynomial Σ_k A^k ⊗ B_k built from the compression of A to E (the orthogonal projection onto E of A restricted to E) to η and then including into the amplification of H gives the same vector as applying the polynomial Σ_k A^k ⊗ B_k built from A itself to ξ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HilbertCrouzeix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HilbertCrouzeix.lean; bytes 5189..5672
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_HilbertCrouzeix

namespace OAI

noncomputable section

open Complex Set

open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

omit [CompleteSpace H] in
theorem exists_finite_compression {m d : ℕ} (A : H →L[ℂ] H)
    (B : Fin (d + 1) → Coeff m) (ξ : H ⊗[ℂ] CoeffSpace m) :
    ∃ (E : Submodule ℂ H) (hE : FiniteDimensional ℂ E),
      letI : FiniteDimensional ℂ E := hE
      ∃ η : Amplification E m,
        tensorInclusion E m η = (↑ξ : Amplification H m) ∧
        tensorInclusion E m (polynomialEval (compression A E) B η) =
          polynomialEval A B (↑ξ) := by
  sorry

end HilbertCrouzeix
end
end OAI
