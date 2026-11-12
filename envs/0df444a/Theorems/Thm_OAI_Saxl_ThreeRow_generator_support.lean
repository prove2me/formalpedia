-- Prove2me | Theorems.Thm_OAI_Saxl_ThreeRow_generator_support
-- name    : OAI.Saxl.ThreeRow.generator_support
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T18:16:03.87158+00:00
-- url     : https://prove2.me/theorems/dc525374-9a97-4bc5-8156-e69828da494a
-- title:
--   OAI.Saxl.ThreeRow.generator_support: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.ThreeRow.generator_support` of [lean/OAI/RepresentationTheory/UniversalSquare/Specht/ThreeRowGenerator.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Specht/ThreeRowGenerator.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.ThreeRow`):
--
--   ```lean
--   theorem generator_support {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
--       (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
--       {ν η μ : YoungDiagram} (tν : Tableau a ν) (tη : Tableau r η) (tμ : Tableau n μ)
--       (hev : ∀ i, Even (ν.rowLen i)) (hν : ν.colLen 0 ≤ 3) (hμ : μ.colLen 0 ≤ 3)
--       (hs : HorizontalStrip ν η) (ht : HorizontalStrip η μ) :
--       ∃ F : Representation.IntertwiningMap (spechtRep tμ)
--         (cyclic (wordRep n 6) (generator q p e)).toRepresentation, F ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.HorizontalStrip` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.ThreeRow.generator` (definitions bundle `OAIQ259US006` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.cyclic`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proof of `OAI.Saxl.Balance.WordPacking.threeRows` of this split imports it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Specht/ThreeRowGenerator.lean (declaration OAI.Saxl.ThreeRow.generator_support)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace Saxl.ThreeRow

theorem generator_support {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    {ν η μ : YoungDiagram} (tν : Tableau a ν) (tη : Tableau r η) (tμ : Tableau n μ)
    (hev : ∀ i, Even (ν.rowLen i)) (hν : ν.colLen 0 ≤ 3) (hμ : μ.colLen 0 ≤ 3)
    (hs : HorizontalStrip ν η) (ht : HorizontalStrip η μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep tμ)
      (cyclic (wordRep n 6) (generator q p e)).toRepresentation, F ≠ 0 := by
  sorry

end Saxl.ThreeRow
end
end

end OAI
end
