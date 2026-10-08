-- Prove2me | Theorems.Thm_OAI_DimensionTen_main_pair
-- name    : OAI.DimensionTen.main_pair
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:34.520271+00:00
-- url     : https://prove2.me/theorems/dc7ff757-fe6e-49d8-98bc-f8ba5b1408bc
-- statement:
--   The theorem states that there exist maps Φ₁ and Φ₂ from 10×10 complex matrices to 10×10 complex matrices, equal to the defined maps phiOne and phiTwo, each of which is PPT, meaning complex-linear, completely positive, and such that composing with the transpose of the output is also completely positive (complete positivity means that applying the map to one factor of any positive semidefinite block matrix on ℂᵏ⊗ℂ¹⁰, for every k≥1, yields a positive semidefinite matrix). Here phiOne sends A to the 6×6 matrix obtained from the transpose of A by embedding it as a symmetric tensor in ℂ⁴⊗ℂ⁴, applying the tensor square of an explicit 4×4 pencil map built from four integer 6×4 blocks, and compressing to the antisymmetric subspace, then padding it to a 10×10 matrix in the first six coordinates. phiTwo is the Hilbert–Schmidt adjoint of an associated complementary map, which uses a Hodge-type complement matrix, applied to the compression of its input onto the first six coordinates. Moreover, letting Z be the Choi matrix of the composition Φ₂∘Φ₁, a 100×100 matrix with entries given by the images of the matrix units, Z is nonzero; no nonzero product vector u⊗v with u,v∈ℂ¹⁰ lies in the range of Z, that is, whenever Z applied to some w∈ℂ¹⁰ˣ¹⁰ equals u⊗v then u=0 or v=0; and Φ₂∘Φ₁ is not entanglement breaking, where entanglement breaking means completely positive and sending every positive semidefinite amplification to a separable matrix, a finite sum of Kronecker products of positive semidefinite matrices. This theorem is admitted in the source, not proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DimensionTenPair.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DimensionTenPair.lean; bytes 4289..4674
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DimensionTenPair

namespace OAI

noncomputable section

open scoped Matrix ComplexOrder

open Matrix Complex

namespace DimensionTen

theorem main_pair :
    ∃ Φ₁ Φ₂ : Mat 10 → Mat 10,
      Φ₁ = phiOne ∧ Φ₂ = phiTwo ∧ PPT Φ₁ ∧ PPT Φ₂ ∧
      (let Z := choi (Φ₂ ∘ Φ₁)
       Z ≠ 0 ∧
       (∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
         Z *ᵥ w = productVector u v → u = 0 ∨ v = 0) ∧
       ¬ EntanglementBreaking (Φ₂ ∘ Φ₁)) := by
  sorry

end DimensionTen
end
end OAI
