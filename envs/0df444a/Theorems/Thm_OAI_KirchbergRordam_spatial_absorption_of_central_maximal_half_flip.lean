-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_spatial_absorption_of_central_maximal_half_flip
-- name    : OAI.KirchbergRordam.spatial_absorption_of_central_maximal_half_flip
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:05:58.43098+00:00
-- url     : https://prove2.me/theorems/a73913bd-171d-49fa-b367-31cb39db5417
-- title:
--   OAI.KirchbergRordam.spatial_absorption_of_central_maximal_half_flip: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.spatial_absorption_of_central_maximal_half_flip` of [lean/OAI/Analysis/CharacterCriterion/TensorComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/TensorComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology BoundedContinuousFunction`, `open Filter Topology`, `open Topology`, `open scoped TensorProduct CStarAlgebra`, `open scoped CStarAlgebra ComplexOrder`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped CStarAlgebra ComplexOrder`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology NormUltrapower`):
--
--   ```lean
--   theorem spatial_absorption_of_central_maximal_half_flip
--       (A D : Type u) [CStarAlgebra A] [CStarAlgebra D]
--       [Nontrivial A] [Nontrivial D]
--       [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace D]
--       (ω : Ultrafilter ℕ) (ι : D →⋆ₐ[ℂ] CentralAlgebra A ω)
--       (u : ℕ → unitary (MaxTensor.Algebra D D))
--       (hu : ∀ d, Tendsto (fun n => Unitary.conjStarAlgAut ℂ _ (u n)
--         (MaxTensor.includeLeft d)) atTop (𝓝 (MaxTensor.includeRight d))) :
--       Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A D)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.MaxTensor.Algebra`, `OAI.KirchbergRordam.MaxTensor.includeLeft`, `OAI.KirchbergRordam.MaxTensor.includeRight`, `OAI.KirchbergRordam.MaxTensor.instNormedAlgebraComplexRaw`, `OAI.KirchbergRordam.MaxTensor.instNormedStarGroupRaw`, `OAI.KirchbergRordam.MaxTensor.instSeminormedRingRaw`, `OAI.KirchbergRordam.GenericRW.StarCompletion.completionStar` and `OAI.KirchbergRordam.GenericRW.StarCompletion.completionStarRing` (definitions bundle `OAIB3Kr007` of this split); `OAI.KirchbergRordam.MaxTensor.Raw`, `OAI.KirchbergRordam.MaxTensor.instAlgebraComplexRaw`, `OAI.KirchbergRordam.MaxTensor.instRingRaw`, `OAI.KirchbergRordam.MaxTensor.instStarRingRaw`, `OAI.KirchbergRordam.MinTensor.Algebra`, `OAI.KirchbergRordam.MinTensor.Raw`, `OAI.KirchbergRordam.MinTensor.instAlgebraComplexRaw`, `OAI.KirchbergRordam.MinTensor.instRingRaw`, `OAI.KirchbergRordam.MinTensor.instSeminormedRingRaw`, `OAI.KirchbergRordam.MinTensor.instStarRingRaw`, `OAI.KirchbergRordam.NormUltrapower.Algebra`, `OAI.KirchbergRordam.NormUltrapower.BoundedSeq`, `OAI.KirchbergRordam.NormUltrapower.CentralAlgebra`, `OAI.KirchbergRordam.NormUltrapower.centralSubringClass`, `OAI.KirchbergRordam.NormUltrapower.nullIdeal`, `OAI.KirchbergRordam.NormUltrapower.nullIdeal_twoSided`, `OAI.KirchbergRordam.NormUltrapower.quotientStar`, `OAI.KirchbergRordam.NormUltrapower.quotientStarModule` and `OAI.KirchbergRordam.NormUltrapower.quotientStarRing` (the published bundle `Def_CharacterCriterion`).
--
--   **Used by.** The proof of `OAI.KirchbergRordam.character_criterion` of this split imports it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/TensorComparison.lean (declaration OAI.KirchbergRordam.spatial_absorption_of_central_maximal_half_flip)

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr007

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
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam
section
universe u
open Filter Topology NormUltrapower

theorem spatial_absorption_of_central_maximal_half_flip
    (A D : Type u) [CStarAlgebra A] [CStarAlgebra D]
    [Nontrivial A] [Nontrivial D]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace D]
    (ω : Ultrafilter ℕ) (ι : D →⋆ₐ[ℂ] CentralAlgebra A ω)
    (u : ℕ → unitary (MaxTensor.Algebra D D))
    (hu : ∀ d, Tendsto (fun n => Unitary.conjStarAlgAut ℂ _ (u n)
      (MaxTensor.includeLeft d)) atTop (𝓝 (MaxTensor.includeRight d))) :
    Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A D) := by
  sorry
end
universe u
open Filter Topology NormUltrapower

end KirchbergRordam

end

end OAI
end
