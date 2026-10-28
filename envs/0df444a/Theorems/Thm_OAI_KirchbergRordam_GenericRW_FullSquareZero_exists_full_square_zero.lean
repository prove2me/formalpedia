-- Prove2me | Theorems.Thm_OAI_KirchbergRordam_GenericRW_FullSquareZero_exists_full_square_zero
-- name    : OAI.KirchbergRordam.GenericRW.FullSquareZero.exists_full_square_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T17:05:09.79969+00:00
-- url     : https://prove2.me/theorems/21882366-64ea-4541-a08c-4d6615500fcd
-- title:
--   OAI.KirchbergRordam.GenericRW.FullSquareZero.exists_full_square_zero: intermediate lemma from OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KirchbergRordam.GenericRW.FullSquareZero.exists_full_square_zero` of [lean/OAI/Analysis/CharacterCriterion/SpatialTensor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/SpatialTensor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KirchbergRordam.GenericRW.FullSquareZero`, with `open scoped TensorProduct`, `open scoped InnerProductSpace`, `open scoped BigOperators`, `open Set Module`, `open Topology`, `open NormedSpace`, `open scoped ComplexOrder`, `open scoped ComplexOrder`, `open scoped InnerProductSpace`, `open scoped InnerProductSpace`, `open NormedSpace`, `open scoped TensorProduct InnerProductSpace`, `open UniformSpace`, `open scoped BigOperators`, `open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor Fullness`):
--
--   ```lean
--   theorem exists_full_square_zero (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
--       ∃ n : ℕ, ∃ y : powerPack D n, y * y = 0 ∧ IsFull y
--   ```
--
--   **Definitions.** The statement is written with `OAI.KirchbergRordam.GenericRW.MaxTensor.CStarPack` (definitions bundle `OAIB3Kr000` of this split); `OAI.KirchbergRordam.GenericRW.Fullness.IsFull` (definitions bundle `OAIB3Kr004` of this split); `OAI.KirchbergRordam.GenericRW.MaxTensor.powerPack` (definitions bundle `OAIB3Kr007` of this split).
--
--   **Used by.** The proof of `OAI.KirchbergRordam.PrimeDropPresentation.stage_to_central` of this split imports it.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/SpatialTensor.lean (declaration OAI.KirchbergRordam.GenericRW.FullSquareZero.exists_full_square_zero)

import Mathlib
import Definitions.Def_OAIB3Kr004
import Definitions.Def_OAIB3Kr007

section

attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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

namespace KirchbergRordam.GenericRW.FullSquareZero
open scoped BigOperators
open _root_.OAI.KirchbergRordam.GenericRW.MaxTensor Fullness
universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

theorem exists_full_square_zero (hD : IsEmpty (D →⋆ₐ[ℂ] ℂ)) :
    ∃ n : ℕ, ∃ y : powerPack D n, y * y = 0 ∧ IsFull y := by
  sorry

end KirchbergRordam.GenericRW.FullSquareZero
end

end OAI
end
