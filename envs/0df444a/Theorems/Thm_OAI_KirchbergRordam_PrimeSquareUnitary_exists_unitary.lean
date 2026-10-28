-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_PrimeSquareUnitary_exists_unitary
-- name    : OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:12:14.113858+00:00
-- url     : https://prove2.me/theorems/7c7b9ae4-5a77-4abc-800c-97ae798ad2a8
-- title:
--   OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary` of [lean/OAI/Analysis/CharacterCriterion/PrimeSquare.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeSquare.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam.PrimeSquareUnitary`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology BoundedContinuousFunction`, `open Filter Topology`, `open Topology`, `open scoped TensorProduct CStarAlgebra`, `open scoped CStarAlgebra ComplexOrder`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped CStarAlgebra ComplexOrder`, `open scoped CStarAlgebra ComplexOrder`, `open MatrixTensor PrimeDimensionDrop PrimeTensorSections FourLegSymmetries`):
--
--   ```lean
--   theorem exists_unitary : ∃ w : unitary (MaxTensor.Algebra (Algebra p q) (Algebra p q)),
--       sectionMap (w : MaxTensor.Algebra (Algebra p q) (Algebra p q))=unitarySection u hu h0
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.MaxTensor.Algebra`, `OAI.KirchbergRordam.MaxTensor.instNormedAlgebraComplexRaw`, `OAI.KirchbergRordam.MaxTensor.instNormedStarGroupRaw`, `OAI.KirchbergRordam.MaxTensor.instSeminormedRingRaw`, `OAI.KirchbergRordam.PrimeTensorSections.Square`, `OAI.KirchbergRordam.GenericRW.StarCompletion.completionStar` and `OAI.KirchbergRordam.GenericRW.StarCompletion.completionStarRing` (definitions bundle `OAIB3Kr007` of this split); `OAI.KirchbergRordam.PrimeTensorSections.SquareFiber` and `OAI.KirchbergRordam.PrimeTensorSections.sectionMap` (definitions bundle `OAIB3Kr010` of this split); `OAI.KirchbergRordam.PrimeSquareUnitary.unitarySection` (definitions bundle `OAIB3Kr014` of this split); `OAI.KirchbergRordam.MaxTensor.Raw`, `OAI.KirchbergRordam.MaxTensor.instAlgebraComplexRaw`, `OAI.KirchbergRordam.MaxTensor.instRingRaw`, `OAI.KirchbergRordam.MaxTensor.instStarRingRaw`, `OAI.KirchbergRordam.PrimeDimensionDrop.Algebra`, and `OAI.KirchbergRordam.PrimeDimensionDrop.Fiber` (the published bundle `Def_CharacterCriterion`).
--
--   **Used by.** The proof of `OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage` of this split imports it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeSquare.lean (declaration OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary)

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr014

section

attribute [-instance] _root_.OAI.KirchbergRordam.MinTensor.instCStarRingAlgebra
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

namespace KirchbergRordam.PrimeSquareUnitary
open scoped CStarAlgebra ComplexOrder
open MatrixTensor PrimeDimensionDrop PrimeTensorSections FourLegSymmetries
variable {p q : ℕ}

variable (u : unitInterval → unitary (Fiber p q)) (hu : Continuous u) (h0 : u 0=1)

theorem exists_unitary : ∃ w : unitary (MaxTensor.Algebra (Algebra p q) (Algebra p q)),
    sectionMap (w : MaxTensor.Algebra (Algebra p q) (Algebra p q))=unitarySection u hu h0 := by
  sorry
end KirchbergRordam.PrimeSquareUnitary

end

end OAI
end
