-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_quotient_isomorphism_of_ultrapower_split_and_conjugacy
-- name    : OAI.KirchbergRordam.quotient_isomorphism_of_ultrapower_split_and_conjugacy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:12:41.753675+00:00
-- url     : https://prove2.me/theorems/69a3400b-a9c3-4958-a393-3f65922f5d5b
-- title:
--   OAI.KirchbergRordam.quotient_isomorphism_of_ultrapower_split_and_conjugacy: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.quotient_isomorphism_of_ultrapower_split_and_conjugacy` of [lean/OAI/Analysis/CharacterCriterion/Absorption.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/Absorption.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology BoundedContinuousFunction`, `open Filter Topology`, `open Topology`, `open scoped TensorProduct CStarAlgebra`, `open scoped CStarAlgebra ComplexOrder`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped CStarAlgebra ComplexOrder`, `open Filter Topology`):
--
--   ```lean
--   theorem quotient_isomorphism_of_ultrapower_split_and_conjugacy
--       {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
--       [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace C]
--       (ω : Ultrafilter ℕ) (φ : A →⋆ₐ[ℂ] B)
--       (q : B →⋆ₐ[ℂ] C) (hq : DenseRange q)
--       (hinj : Function.Injective (q.comp φ))
--       (ψ : B →⋆ₐ[ℂ] NormUltrapower.Algebra A ω)
--       (hsplit : ∀ a, ψ (φ a) = NormUltrapower.diagonal ω a)
--       (hconj : ∀ (T : Finset B) (ε : ℝ), 0 < ε →
--         ∃ u : unitary (NormUltrapower.Algebra B ω), ∀ b ∈ T,
--           dist (Unitary.conjStarAlgAut ℂ _ u (NormUltrapower.map φ ω (ψ b)))
--             (NormUltrapower.diagonal ω b) < ε) :
--       Nonempty (A ≃⋆ₐ[ℂ] C)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.GenericRW.DetectingSpace.quotientNormedRing` (definitions bundle `OAIB3Kr009` of this split); `OAI.KirchbergRordam.NormUltrapower.map` (definitions bundle `OAIB3Kr012` of this split); `OAI.KirchbergRordam.NormUltrapower.Algebra`, `OAI.KirchbergRordam.NormUltrapower.BoundedSeq`, `OAI.KirchbergRordam.NormUltrapower.diagonal`, `OAI.KirchbergRordam.NormUltrapower.nullIdeal`, `OAI.KirchbergRordam.NormUltrapower.nullIdeal_closed`, `OAI.KirchbergRordam.NormUltrapower.nullIdeal_twoSided`, `OAI.KirchbergRordam.NormUltrapower.quotientStar` and `OAI.KirchbergRordam.NormUltrapower.quotientStarRing` (the published bundle `Def_CharacterCriterion`).
--
--   **Used by.** The proof of `OAI.KirchbergRordam.spatial_absorption_of_central_maximal_half_flip` of this split imports it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/Absorption.lean (declaration OAI.KirchbergRordam.quotient_isomorphism_of_ultrapower_split_and_conjugacy)

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam

open Filter Topology

theorem quotient_isomorphism_of_ultrapower_split_and_conjugacy
    {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace C]
    (ω : Ultrafilter ℕ) (φ : A →⋆ₐ[ℂ] B)
    (q : B →⋆ₐ[ℂ] C) (hq : DenseRange q)
    (hinj : Function.Injective (q.comp φ))
    (ψ : B →⋆ₐ[ℂ] NormUltrapower.Algebra A ω)
    (hsplit : ∀ a, ψ (φ a) = NormUltrapower.diagonal ω a)
    (hconj : ∀ (T : Finset B) (ε : ℝ), 0 < ε →
      ∃ u : unitary (NormUltrapower.Algebra B ω), ∀ b ∈ T,
        dist (Unitary.conjStarAlgAut ℂ _ u (NormUltrapower.map φ ω (ψ b)))
          (NormUltrapower.diagonal ω b) < ε) :
    Nonempty (A ≃⋆ₐ[ℂ] C) := by
  sorry
end KirchbergRordam

end

end OAI
end
