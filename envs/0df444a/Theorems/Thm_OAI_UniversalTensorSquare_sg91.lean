-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg91
-- name    : OAI.UniversalTensorSquare.sg91
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:56:01.106294+00:00
-- url     : https://prove2.me/theorems/01f837d3-8d0d-4ef6-ad20-ea26fbe4a27f
-- title:
--   OAI.UniversalTensorSquare.sg91: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg91` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg91 : RowSquare [4,1,1] [3,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree22_4All`, `OAI.UniversalTensorSquare.degreeTree26_11All`, `OAI.UniversalTensorSquare.degreeTree26_19All`, `OAI.UniversalTensorSquare.degreeTree26_41All`, `OAI.UniversalTensorSquare.degree_pos26`, `OAI.UniversalTensorSquare.sg2063`, `OAI.UniversalTensorSquare.sg21036`, `OAI.UniversalTensorSquare.sg2636`, `OAI.UniversalTensorSquare.sg29986`, `OAI.UniversalTensorSquare.sg35543`, `OAI.UniversalTensorSquare.sg35589`, `OAI.UniversalTensorSquare.sg35754`, `OAI.UniversalTensorSquare.sg35755`, `OAI.UniversalTensorSquare.sg36405`, `OAI.UniversalTensorSquare.sg36406`, `OAI.UniversalTensorSquare.sg36635`, `OAI.UniversalTensorSquare.sg36718`, `OAI.UniversalTensorSquare.sg37816`, `OAI.UniversalTensorSquare.sg38003`, `OAI.UniversalTensorSquare.sg38011`, `OAI.UniversalTensorSquare.sg38070`, `OAI.UniversalTensorSquare.sg38088`, `OAI.UniversalTensorSquare.sg38557`, `OAI.UniversalTensorSquare.sg39036`, `OAI.UniversalTensorSquare.sg39222`, `OAI.UniversalTensorSquare.sg39830`, `OAI.UniversalTensorSquare.sg41659`, `OAI.UniversalTensorSquare.sg41668`, `OAI.UniversalTensorSquare.sg41694`, `OAI.UniversalTensorSquare.sg41700`, `OAI.UniversalTensorSquare.sg42093`, `OAI.UniversalTensorSquare.sg42128`, `OAI.UniversalTensorSquare.sg42248` and `OAI.UniversalTensorSquare.sg42797` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg91)

import Mathlib
import Definitions.Def_OAIQ259US007

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

lemma sg91 : RowSquare [4,1,1] [3,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
