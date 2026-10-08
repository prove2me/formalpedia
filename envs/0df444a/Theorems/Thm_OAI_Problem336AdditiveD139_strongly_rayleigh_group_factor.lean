-- Prove2me | Theorems.Thm_OAI_Problem336AdditiveD139_strongly_rayleigh_group_factor
-- name    : OAI.Problem336AdditiveD139.strongly_rayleigh_group_factor
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:08.579911+00:00
-- url     : https://prove2.me/theorems/e9ef6a16-93bc-40bd-837b-d0d38896fa37
-- statement:
--   The theorem states that, for every countable group Γ equipped with a measurable space structure, and every probability measure μ on the space of Boolean-valued configurations Γ → Bool, if μ is strongly Rayleigh in the countable sense and invariant under left translation, then μ has an equivariant i.i.d. factor. Strongly Rayleigh (countable) means that for every finite subset S of Γ and every assignment z of complex numbers with strictly positive imaginary part to the points of S, the multivariate generating polynomial of the marginal law of μ on S, namely the sum over x : S → Bool of μ(configurations agreeing with x on S) times the product of z_i over those i with x_i true, is nonzero. Invariance means that for each g in Γ, the pushforward of μ under the left translation (g·a)(h) = a(g⁻¹h) equals μ. Having an equivariant i.i.d. factor means there is a measurable map Φ from Γ → [0,1] to Γ → Bool that commutes with left translation by every g at every point, and that pushes the product of Lebesgue (uniform) measures on [0,1], indexed by Γ, forward to μ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StronglyRayleighDPP.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StronglyRayleighDPP.lean; bytes 5717..5986
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

theorem strongly_rayleigh_group_factor :
    ∀ (Γ : Type u_2) [Group Γ] [Countable Γ] [MeasurableSpace Γ],
      ∀ μ : ProbabilityMeasure (Γ → Bool),
        StronglyRayleighCountable μ → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ := by
  sorry

end Problem336AdditiveD139
end
end OAI
