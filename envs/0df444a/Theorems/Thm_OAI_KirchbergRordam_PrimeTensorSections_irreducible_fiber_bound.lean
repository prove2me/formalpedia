-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_PrimeTensorSections_irreducible_fiber_bound
-- name    : OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:10:40.561771+00:00
-- url     : https://prove2.me/theorems/5480af58-23df-4c67-b327-8a244e533262
-- title:
--   OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound` of [lean/OAI/Analysis/CharacterCriterion/TensorSections.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/TensorSections.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam.PrimeTensorSections`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology BoundedContinuousFunction`, `open Filter Topology`, `open Topology`, `open scoped TensorProduct CStarAlgebra`, `open scoped CStarAlgebra ComplexOrder`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped CStarAlgebra ComplexOrder TensorProduct`, `open PrimeDimensionDrop MatrixTensor`):
--
--   ```lean
--   lemma irreducible_fiber_bound
--       (π : IrreducibleRepresentation (MaxTensor.Algebra (Algebra p q) (Algebra r k))) :
--       ∃ s t : unitInterval, ∀ x, ‖π.representation x‖ ≤ ‖sectionMap x (s,t)‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.IrreducibleRepresentation` (definitions bundle `OAIB3Kr004` of this split); `OAI.KirchbergRordam.MaxTensor.Algebra`, `OAI.KirchbergRordam.MaxTensor.instCStarAlgebraAlgebra`, `OAI.KirchbergRordam.MaxTensor.instNormedAlgebraComplexRaw`, `OAI.KirchbergRordam.MaxTensor.instSeminormedRingRaw`, `OAI.KirchbergRordam.PrimeTensorSections.Square` and `OAI.KirchbergRordam.GenericRW.StarCompletion.completionStar` (definitions bundle `OAIB3Kr007` of this split); `OAI.KirchbergRordam.PrimeTensorSections.SquareFiber` and `OAI.KirchbergRordam.PrimeTensorSections.sectionMap` (definitions bundle `OAIB3Kr010` of this split); `OAI.KirchbergRordam.MaxTensor.Raw`, `OAI.KirchbergRordam.MaxTensor.instAlgebraComplexRaw`, `OAI.KirchbergRordam.MaxTensor.instRingRaw`, `OAI.KirchbergRordam.MaxTensor.instStarRingRaw`, `OAI.KirchbergRordam.PrimeDimensionDrop.Algebra`, and `OAI.KirchbergRordam.PrimeDimensionDrop.Fiber` (the published bundle `Def_CharacterCriterion`).
--
--   **Used by.** The proofs of `OAI.KirchbergRordam.PrimeDropPresentation.HalfFlip.finite_stage`, `OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary` and `OAI.KirchbergRordam.PrimeTensorSections.sectionRange_scalar` of this split import it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/TensorSections.lean (declaration OAI.KirchbergRordam.PrimeTensorSections.irreducible_fiber_bound)

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr004
import Definitions.Def_OAIB3Kr010

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

namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor
variable {p q r k : ℕ}

lemma irreducible_fiber_bound
    (π : IrreducibleRepresentation (MaxTensor.Algebra (Algebra p q) (Algebra r k))) :
    ∃ s t : unitInterval, ∀ x, ‖π.representation x‖ ≤ ‖sectionMap x (s,t)‖ := by
  sorry

end KirchbergRordam.PrimeTensorSections
end

end OAI
end
