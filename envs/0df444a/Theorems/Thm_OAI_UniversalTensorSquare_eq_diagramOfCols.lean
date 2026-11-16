-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_eq_diagramOfCols
-- name    : OAI.UniversalTensorSquare.eq_diagramOfCols
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:31:27.093203+00:00
-- url     : https://prove2.me/theorems/08faf9d5-30ee-4d8e-8ae5-4a5c0726da13
-- title:
--   OAI.UniversalTensorSquare.eq_diagramOfCols: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.eq_diagramOfCols` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/FiniteDiagrams.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/FiniteDiagrams.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`):
--
--   ```lean
--   lemma eq_diagramOfCols (μ : YoungDiagram) (rs : List ℕ) (hs : rs.SortedGE)
--       (h : μ.transpose.rowLens = rs) : μ = diagramOfCols rs hs
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.diagramOfCols` (definitions bundle `OAIQ259US002` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_123All`, `OAI.UniversalTensorSquare.degreeTree39_13All`, `OAI.UniversalTensorSquare.degreeTree39_14All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree41_9All`, `OAI.UniversalTensorSquare.degreeTree43_112All`, `OAI.UniversalTensorSquare.five_kronecker_pos` and `OAI.UniversalTensorSquare.seven_kronecker_pos` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/FiniteDiagrams.lean (declaration OAI.UniversalTensorSquare.eq_diagramOfCols)

import Mathlib
import Definitions.Def_OAIQ259US002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare

lemma eq_diagramOfCols (μ : YoungDiagram) (rs : List ℕ) (hs : rs.SortedGE)
    (h : μ.transpose.rowLens = rs) : μ = diagramOfCols rs hs := by
  sorry

end UniversalTensorSquare
end

end OAI
end
