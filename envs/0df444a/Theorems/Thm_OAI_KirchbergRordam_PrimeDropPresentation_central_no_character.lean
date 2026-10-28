-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_PrimeDropPresentation_central_no_character
-- name    : OAI.KirchbergRordam.PrimeDropPresentation.central_no_character
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:10:09.544658+00:00
-- url     : https://prove2.me/theorems/6b557ad5-efd2-4479-81cf-291a86ab5630
-- title:
--   OAI.KirchbergRordam.PrimeDropPresentation.central_no_character: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.PrimeDropPresentation.central_no_character` of [lean/OAI/Analysis/CharacterCriterion/PrimeChannels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeChannels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam.PrimeDropPresentation`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology BoundedContinuousFunction`, `open Filter Topology`, `open Topology`, `open scoped TensorProduct CStarAlgebra`, `open scoped CStarAlgebra ComplexOrder`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped CStarAlgebra ComplexOrder`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter`):
--
--   ```lean
--   theorem central_no_character (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
--       IsEmpty (NormUltrapower.CentralAlgebra S.Algebra ω →⋆ₐ[ℂ] ℂ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.PrimeDropPresentation.Algebra` and `OAI.KirchbergRordam.PrimeDropPresentation.instCStarAlgebraAlgebra` (definitions bundle `OAIB3Kr012` of this split); `OAI.KirchbergRordam.PrimeDropPresentation`, `OAI.KirchbergRordam.NormUltrapower.Algebra`, `OAI.KirchbergRordam.NormUltrapower.BoundedSeq`, `OAI.KirchbergRordam.NormUltrapower.CentralAlgebra`, `OAI.KirchbergRordam.NormUltrapower.centralSubringClass`, `OAI.KirchbergRordam.NormUltrapower.nullIdeal`, `OAI.KirchbergRordam.NormUltrapower.nullIdeal_twoSided`, `OAI.KirchbergRordam.NormUltrapower.quotientStar`, `OAI.KirchbergRordam.NormUltrapower.quotientStarModule` and `OAI.KirchbergRordam.NormUltrapower.quotientStarRing` (the published bundle `Def_CharacterCriterion`).
--
--   **Used by.** The proof of `OAI.KirchbergRordam.character_criterion` of this split imports it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeChannels.lean (declaration OAI.KirchbergRordam.PrimeDropPresentation.central_no_character)

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
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.PrimeDropPresentation
open Filter
variable (S : PrimeDropPresentation)

theorem central_no_character (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (NormUltrapower.CentralAlgebra S.Algebra ω →⋆ₐ[ℂ] ℂ) := by
  sorry

end KirchbergRordam.PrimeDropPresentation
end

end OAI
end
