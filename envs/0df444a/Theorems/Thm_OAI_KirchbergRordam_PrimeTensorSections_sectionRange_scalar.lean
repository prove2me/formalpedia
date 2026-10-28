-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_PrimeTensorSections_sectionRange_scalar
-- name    : OAI.KirchbergRordam.PrimeTensorSections.sectionRange_scalar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:16:38.134016+00:00
-- url     : https://prove2.me/theorems/9b9b2367-6dfe-4d5f-bfc9-c039d2c35c5c
-- title:
--   OAI.KirchbergRordam.PrimeTensorSections.sectionRange_scalar: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.PrimeTensorSections.sectionRange_scalar` of [lean/OAI/Analysis/CharacterCriterion/TensorSections.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/TensorSections.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam.PrimeTensorSections`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology BoundedContinuousFunction`, `open Filter Topology`, `open Topology`, `open scoped TensorProduct CStarAlgebra`, `open scoped CStarAlgebra ComplexOrder`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped CStarAlgebra ComplexOrder TensorProduct`, `open PrimeDimensionDrop MatrixTensor ContinuousSectionLocality`):
--
--   ```lean
--   lemma sectionRange_scalar (f : C(Square,ℂ)) :
--       scalarMap f∈sectionRange (p:=p) (q:=q) (r:=r) (k:=k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.PrimeTensorSections.Square` (definitions bundle `OAIB3Kr007` of this split); `OAI.KirchbergRordam.ContinuousSectionLocality.scalarMap` (definitions bundle `OAIB3Kr008` of this split); `OAI.KirchbergRordam.PrimeTensorSections.SquareFiber` (definitions bundle `OAIB3Kr010` of this split); `OAI.KirchbergRordam.PrimeTensorSections.sectionRange` (definitions bundle `OAIB3Kr014` of this split).
--
--   **Used by.** The proof of `OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary` of this split imports it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/TensorSections.lean (declaration OAI.KirchbergRordam.PrimeTensorSections.sectionRange_scalar)

import Mathlib
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

namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor ContinuousSectionLocality
variable {p q r k : ℕ}

lemma sectionRange_scalar (f : C(Square,ℂ)) :
    scalarMap f∈sectionRange (p:=p) (q:=q) (r:=r) (k:=k) := by
  sorry

end KirchbergRordam.PrimeTensorSections
end

end OAI
end
