-- Prove2me | Theorems.Thm_OAI_Heisenberg_finiteRepresentation_field
-- name    : OAI.Heisenberg.finiteRepresentation_field
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T08:29:38.707927+00:00
-- url     : https://prove2.me/theorems/e7251bbd-1d0b-446f-9cb6-94663bad4683
-- title:
--   OAI.Heisenberg.finiteRepresentation_field: intermediate lemma from OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Heisenberg.finiteRepresentation_field` of [lean/OAI/MathematicalPhysics/Heisenberg/SpinField.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinField.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Heisenberg`, with `open scoped Classical BigOperators Matrix Matrix.Norms.Operator`, `open SlotTensor TensorMatrix`):
--
--   ```lean
--   lemma finiteRepresentation_field (Λ : Finset (Site d)) (h : ℝ) :
--       finiteRepresentation (ℓ:=ℓ) (fun x : Λ=>x.val) Subtype.val_injective
--         ((-1/2:ℝ) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ-
--           h • Matrix.diagonal (physicalMagnetization (X:=Λ) ℓ))=shiftedField Λ h
--   ```
--
--   **Definitions.** The statement is written with `OAI.Heisenberg.finiteRepresentation`, `OAI.Heisenberg.quasiLocalNormedAlgebra`, `OAI.Heisenberg.shiftedField`, `OAI.Heisenberg.SlotTensor.physicalMagnetization` and `OAI.Heisenberg.SlotTensor.spinGenerator` (definitions bundle `OAIW2HM000` of this split); `OAI.Heisenberg.Configuration`, `OAI.Heisenberg.Level`, `OAI.Heisenberg.NearestNeighbor`, `OAI.Heisenberg.QuasiLocal`, `OAI.Heisenberg.Site`, `OAI.Heisenberg.SpinHilbert` and `OAI.Heisenberg.SpinOperator` (the published bundle `Def_Heisenberg`).
--
--   **Used by.** The proof of `OAI.Heisenberg.Selection.physical_field_mean` of this split imports it.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinField.lean (declaration OAI.Heisenberg.finiteRepresentation_field)

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open SlotTensor TensorMatrix
variable {d ℓ : ℕ}

lemma finiteRepresentation_field (Λ : Finset (Site d)) (h : ℝ) :
    finiteRepresentation (ℓ:=ℓ) (fun x : Λ=>x.val) Subtype.val_injective
      ((-1/2:ℝ) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ-
        h • Matrix.diagonal (physicalMagnetization (X:=Λ) ℓ))=shiftedField Λ h := by
  sorry

end Heisenberg
end
end

end OAI
end
