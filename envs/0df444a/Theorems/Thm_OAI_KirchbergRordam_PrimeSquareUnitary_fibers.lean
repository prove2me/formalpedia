-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_PrimeSquareUnitary_fibers
-- name    : OAI.KirchbergRordam.PrimeSquareUnitary.fibers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:12:12.531192+00:00
-- url     : https://prove2.me/theorems/593df721-4fd9-4dd9-a67e-c0ee917af45b
-- title:
--   OAI.KirchbergRordam.PrimeSquareUnitary.fibers: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.PrimeSquareUnitary.fibers` of [lean/OAI/Analysis/CharacterCriterion/PrimeSquare.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeSquare.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam.PrimeSquareUnitary`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open Filter Topology BoundedContinuousFunction`, `open Filter Topology`, `open Topology`, `open scoped TensorProduct CStarAlgebra`, `open scoped CStarAlgebra ComplexOrder`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped CStarAlgebra ComplexOrder`, `open scoped CStarAlgebra ComplexOrder`, `open MatrixTensor PrimeDimensionDrop PrimeTensorSections FourLegSymmetries`):
--
--   ```lean
--   lemma fibers (x : Square) : ((diagram u hu h0).W x:(SquareFiber p q p q))∈fiberRange (p:=p) (q:=q) (r:=p) (k:=q) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.SymmetryConjugacyDiagram.Data.W` (definitions bundle `OAIB3Kr004` of this split); `OAI.KirchbergRordam.PrimeTensorSections.Square` (definitions bundle `OAIB3Kr007` of this split); `OAI.KirchbergRordam.PrimeTensorSections.SquareFiber` (definitions bundle `OAIB3Kr010` of this split); `OAI.KirchbergRordam.PrimeSquareUnitary.diagram` and `OAI.KirchbergRordam.PrimeTensorSections.fiberRange` (definitions bundle `OAIB3Kr014` of this split); `OAI.KirchbergRordam.PrimeDimensionDrop.Fiber` (the published bundle `Def_CharacterCriterion`).
--
--   **Used by.** The proof of `OAI.KirchbergRordam.PrimeSquareUnitary.exists_unitary` of this split imports it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeSquare.lean (declaration OAI.KirchbergRordam.PrimeSquareUnitary.fibers)

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr014

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

namespace KirchbergRordam.PrimeSquareUnitary
open scoped CStarAlgebra ComplexOrder
open MatrixTensor PrimeDimensionDrop PrimeTensorSections FourLegSymmetries
variable {p q : ℕ}

variable (u : unitInterval → unitary (Fiber p q)) (hu : Continuous u) (h0 : u 0=1)

lemma fibers (x : Square) : ((diagram u hu h0).W x:(SquareFiber p q p q))∈fiberRange (p:=p) (q:=q) (r:=p) (k:=q) x := by
  sorry

end KirchbergRordam.PrimeSquareUnitary

end

end OAI
end
