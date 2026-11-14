-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
-- name    : OAI.UniversalTensorSquare.rowDiagram_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:33:19.845925+00:00
-- url     : https://prove2.me/theorems/7f6b8e19-f481-4d9d-9abf-4e5f3833a490
-- title:
--   OAI.UniversalTensorSquare.rowDiagram_eq: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.rowDiagram_eq` of [lean/OAI/RepresentationTheory/UniversalSquare/Contraction/RowCertificates.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/RowCertificates.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma rowDiagram_eq (rs : List ℕ) (h : GoodRows rs) :
--       rowDiagram rs = YoungDiagram.ofRowLens rs h.1
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.GoodRows` and `OAI.UniversalTensorSquare.rowDiagram` (definitions bundle `OAIQ259US001` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_15All`, `OAI.UniversalTensorSquare.degreeTree39_16All`, `OAI.UniversalTensorSquare.degreeTree39_19All`, `OAI.UniversalTensorSquare.degreeTree43_103All`, `OAI.UniversalTensorSquare.degreeTree43_10All`, `OAI.UniversalTensorSquare.degreeTree43_155All`, `OAI.UniversalTensorSquare.sg10131`, `OAI.UniversalTensorSquare.sg21949`, `OAI.UniversalTensorSquare.sg23699`, `OAI.UniversalTensorSquare.sg23706`, `OAI.UniversalTensorSquare.sg25195`, `OAI.UniversalTensorSquare.sg25304`, `OAI.UniversalTensorSquare.sg25311`, `OAI.UniversalTensorSquare.sg25500`, `OAI.UniversalTensorSquare.sg25505`, `OAI.UniversalTensorSquare.sg25554`, `OAI.UniversalTensorSquare.sg25566`, `OAI.UniversalTensorSquare.sg25571`, `OAI.UniversalTensorSquare.sg25576`, `OAI.UniversalTensorSquare.sg25613`, `OAI.UniversalTensorSquare.sg25683`, `OAI.UniversalTensorSquare.sg25684`, `OAI.UniversalTensorSquare.sg25685`, `OAI.UniversalTensorSquare.sg25688`, `OAI.UniversalTensorSquare.sg25689`, `OAI.UniversalTensorSquare.sg25700`, `OAI.UniversalTensorSquare.sg25701`, `OAI.UniversalTensorSquare.sg26008`, `OAI.UniversalTensorSquare.sg26009`, `OAI.UniversalTensorSquare.sg26011`, `OAI.UniversalTensorSquare.sg5`, `OAI.UniversalTensorSquare.sg543`, `OAI.UniversalTensorSquare.sg6472`, `OAI.UniversalTensorSquare.sg6563`, `OAI.UniversalTensorSquare.sg6652`, `OAI.UniversalTensorSquare.sg6691`, `OAI.UniversalTensorSquare.sg8117`, `OAI.UniversalTensorSquare.sg8415`, `OAI.UniversalTensorSquare.sg8418` and `OAI.UniversalTensorSquare.sg9100` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/RowCertificates.lean (declaration OAI.UniversalTensorSquare.rowDiagram_eq)

import Mathlib
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowDiagram_eq (rs : List ℕ) (h : GoodRows rs) :
    rowDiagram rs = YoungDiagram.ofRowLens rs h.1 := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
