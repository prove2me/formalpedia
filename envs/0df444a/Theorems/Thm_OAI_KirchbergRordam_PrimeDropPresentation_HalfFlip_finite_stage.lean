-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_PrimeDropPresentation_HalfFlip_finite_stage
-- name    : OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:10:02.466598+00:00
-- url     : https://prove2.me/theorems/c1c10b05-5cdf-4ca3-bf05-953f15d328c8
-- title:
--   OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage` of [lean/OAI/Analysis/CharacterCriterion/PrimePresentation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimePresentation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology BoundedContinuousFunction`, `open Filter Topology`, `open Topology`, `open scoped TensorProduct CStarAlgebra`, `open scoped CStarAlgebra ComplexOrder`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped CStarAlgebra ComplexOrder`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open scoped CStarAlgebra ComplexOrder`, `open Filter Topology`, `open UnitaryDisplacement`):
--
--   ```lean
--   lemma finite_stage (n : ℕ) (F : Finset (S.Stage n)) (ε : ℝ) (hε : 0<ε) :
--       ∃ w : unitary (MaxTensor.Algebra S.Algebra S.Algebra), ∀ f∈F,
--         ‖conj w (MaxTensor.includeLeft (S.inclusion n f))-
--           MaxTensor.includeRight (S.inclusion n f)‖≤ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.UnitaryDisplacement.conj` (definitions bundle `OAIB3Kr004` of this split); `OAI.KirchbergRordam.MaxTensor.Algebra`, `OAI.KirchbergRordam.MaxTensor.includeLeft`, `OAI.KirchbergRordam.MaxTensor.includeRight`, `OAI.KirchbergRordam.MaxTensor.instCStarAlgebraAlgebra`, `OAI.KirchbergRordam.MaxTensor.instNormedAlgebraComplexRaw`, `OAI.KirchbergRordam.MaxTensor.instNormedStarGroupRaw`, `OAI.KirchbergRordam.MaxTensor.instSeminormedRingRaw`, `OAI.KirchbergRordam.GenericRW.StarCompletion.completionStar` and `OAI.KirchbergRordam.GenericRW.StarCompletion.completionStarRing` (definitions bundle `OAIB3Kr007` of this split); `OAI.KirchbergRordam.PrimeDropPresentation.Algebra`, `OAI.KirchbergRordam.PrimeDropPresentation.inclusion` and `OAI.KirchbergRordam.PrimeDropPresentation.instCStarAlgebraAlgebra` (definitions bundle `OAIB3Kr012` of this split); `OAI.KirchbergRordam.PrimeDropPresentation`, `OAI.KirchbergRordam.MaxTensor.Raw`, `OAI.KirchbergRordam.MaxTensor.instAlgebraComplexRaw`, `OAI.KirchbergRordam.MaxTensor.instRingRaw`, `OAI.KirchbergRordam.MaxTensor.instStarRingRaw`, `OAI.KirchbergRordam.PrimeDropPresentation.Stage` and `OAI.KirchbergRordam.PrimeDropPresentation.instCStarAlgebraStage` (the published bundle `Def_CharacterCriterion`).
--
--   **Used by.** The proof of `OAI.KirchbergRordam.character_criterion` of this split imports it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimePresentation.lean (declaration OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage)

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

namespace KirchbergRordam.PrimeDropPresentation.HalfFlip
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open UnitaryDisplacement
variable (S : PrimeDropPresentation)
lemma finite_stage (n : ℕ) (F : Finset (S.Stage n)) (ε : ℝ) (hε : 0<ε) :
    ∃ w : unitary (MaxTensor.Algebra S.Algebra S.Algebra), ∀ f∈F,
      ‖conj w (MaxTensor.includeLeft (S.inclusion n f))-
        MaxTensor.includeRight (S.inclusion n f)‖≤ε := by
  sorry

end KirchbergRordam.PrimeDropPresentation.HalfFlip
end

end OAI
end
