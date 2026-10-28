-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_MatrixTensor_representation_bound
-- name    : OAI.KirchbergRordam.MatrixTensor.representation_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:04:23.790756+00:00
-- url     : https://prove2.me/theorems/331e0271-70e0-4957-b1f0-e8fb05a93987
-- title:
--   OAI.KirchbergRordam.MatrixTensor.representation_bound: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.MatrixTensor.representation_bound` of [lean/OAI/Analysis/CharacterCriterion/PrimeSpectrum.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeSpectrum.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam.MatrixTensor`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology BoundedContinuousFunction`, `open Filter Topology`, `open Topology`, `open scoped TensorProduct CStarAlgebra`, `open scoped CStarAlgebra ComplexOrder`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped CStarAlgebra ComplexOrder TensorProduct`):
--
--   ```lean
--   theorem representation_bound
--       (eL : A →⋆ₐ[ℂ] Mat ι) (eR : B →⋆ₐ[ℂ] Mat κ)
--       (π : MaxTensor.Algebra A B →⋆ₐ[ℂ] R)
--       (hkL : ∀ a, eL a=0 → π (MaxTensor.includeLeft a)=0)
--       (hkR : ∀ b, eR b=0 → π (MaxTensor.includeRight b)=0) :
--       ∀ x, ‖π x‖≤‖fiberMap eL eR x‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.MatrixTensor.fiberMap`, `OAI.KirchbergRordam.MaxTensor.Algebra`, `OAI.KirchbergRordam.MaxTensor.includeLeft`, `OAI.KirchbergRordam.MaxTensor.includeRight`, `OAI.KirchbergRordam.MaxTensor.instNormedAlgebraComplexRaw`, `OAI.KirchbergRordam.MaxTensor.instSeminormedRingRaw` and `OAI.KirchbergRordam.GenericRW.StarCompletion.completionStar` (definitions bundle `OAIB3Kr007` of this split); `OAI.KirchbergRordam.MatrixTensor.Mat`, `OAI.KirchbergRordam.MaxTensor.Raw`, `OAI.KirchbergRordam.MaxTensor.instAlgebraComplexRaw`, `OAI.KirchbergRordam.MaxTensor.instRingRaw` and `OAI.KirchbergRordam.MaxTensor.instStarRingRaw` (the published bundle `Def_CharacterCriterion`).
--
--   **Used by.** The proof of `OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound` of this split imports it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeSpectrum.lean (declaration OAI.KirchbergRordam.MatrixTensor.representation_bound)

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

namespace KirchbergRordam.MatrixTensor
open scoped CStarAlgebra ComplexOrder TensorProduct
variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem representation_bound
    (eL : A →⋆ₐ[ℂ] Mat ι) (eR : B →⋆ₐ[ℂ] Mat κ)
    (π : MaxTensor.Algebra A B →⋆ₐ[ℂ] R)
    (hkL : ∀ a, eL a=0 → π (MaxTensor.includeLeft a)=0)
    (hkR : ∀ b, eR b=0 → π (MaxTensor.includeRight b)=0) :
    ∀ x, ‖π x‖≤‖fiberMap eL eR x‖ := by
  sorry
end KirchbergRordam.MatrixTensor

end

end OAI
end
