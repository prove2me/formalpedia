-- Prove2me | Theorems.Thm_OAI_Problem336AdditiveD139_invariant_positive_contraction_dpp_factor
-- name    : OAI.Problem336AdditiveD139.invariant_positive_contraction_dpp_factor
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:08.459864+00:00
-- url     : https://prove2.me/theorems/244c509c-d273-4610-9838-546b5aa05ce2
-- statement:
--   The theorem states that for every countable group Γ equipped with a measurable space structure, every complex kernel K : Γ × Γ → ℂ, and every probability measure μ on the space of binary configurations Γ → Bool, the following holds. Suppose K is a positive contraction kernel, meaning K(i,j) equals the complex conjugate of K(j,i) and, for every finite subset S of Γ and every complex vector c on S, the real part of the sum over i,j in S of conj(c_i) K(i,j) c_j lies between 0 and the sum of |c_i|². Suppose also μ is a determinantal law for K, meaning that for every finite set A ⊆ Γ, the probability that x_i = true for all i in A equals det(K(i,j)) over i,j in A. Suppose finally μ is invariant, meaning that for every g ∈ Γ the pushforward of μ under the left translation a ↦ (h ↦ a(g⁻¹h)) is μ itself. Then μ has an equivariant iid factor: there is a measurable map Phi from Γ → [0,1] to Γ → Bool that commutes with left translation by every group element and sends the product of Lebesgue measures on [0,1] (iid uniform labels indexed by Γ) to μ. The theorem is stated with its proof admitted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StronglyRayleighDPP.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StronglyRayleighDPP.lean; bytes 6632..6966
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_StronglyRayleighDPP

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12

universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139

theorem invariant_positive_contraction_dpp_factor :
    ∀ (Γ : Type u_5) [Group Γ] [Countable Γ] [MeasurableSpace Γ]
      (K : Γ → Γ → ℂ) (μ : ProbabilityMeasure (Γ → Bool)),
      PositiveContractionKernel K → IsDeterminantalLaw μ K →
        InvariantBinaryLaw μ → HasEquivariantIIDFactor μ := by
  sorry

end Problem336AdditiveD139
end
end OAI
