-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg238
-- name    : OAI.UniversalTensorSquare.sg238
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T01:28:39.714452+00:00
-- url     : https://prove2.me/theorems/9fa99cb3-2e4c-4a32-afe2-d3415b412d0d
-- title:
--   OAI.UniversalTensorSquare.sg238: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg238` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg238 : RowSquare [2,1,1,1,1,1,1] [8]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_128All`, `OAI.UniversalTensorSquare.degreeTree62_131All`, `OAI.UniversalTensorSquare.degreeTree62_134All`, `OAI.UniversalTensorSquare.degreeTree62_162All`, `OAI.UniversalTensorSquare.degreeTree62_170All`, `OAI.UniversalTensorSquare.degreeTree62_198All`, `OAI.UniversalTensorSquare.degreeTree62_201All`, `OAI.UniversalTensorSquare.degreeTree62_205All`, `OAI.UniversalTensorSquare.degreeTree62_221All`, `OAI.UniversalTensorSquare.degreeTree62_226All`, `OAI.UniversalTensorSquare.degreeTree62_227All`, `OAI.UniversalTensorSquare.degreeTree62_238All`, `OAI.UniversalTensorSquare.degreeTree62_246All`, `OAI.UniversalTensorSquare.degreeTree62_266All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_294All`, `OAI.UniversalTensorSquare.degreeTree62_304All`, `OAI.UniversalTensorSquare.degreeTree62_306All`, `OAI.UniversalTensorSquare.degreeTree62_32All`, `OAI.UniversalTensorSquare.degreeTree62_35All`, `OAI.UniversalTensorSquare.degreeTree62_42All`, `OAI.UniversalTensorSquare.degreeTree62_437All`, `OAI.UniversalTensorSquare.degreeTree62_43All`, `OAI.UniversalTensorSquare.degreeTree62_464All`, `OAI.UniversalTensorSquare.degreeTree62_46All`, `OAI.UniversalTensorSquare.degreeTree62_50All`, `OAI.UniversalTensorSquare.degreeTree62_542All`, `OAI.UniversalTensorSquare.degreeTree62_56All`, `OAI.UniversalTensorSquare.degreeTree62_728All`, `OAI.UniversalTensorSquare.degreeTree62_758All`, `OAI.UniversalTensorSquare.degreeTree62_89All`, `OAI.UniversalTensorSquare.degreeTree62_917All`, `OAI.UniversalTensorSquare.degreeTree62_922All`, `OAI.UniversalTensorSquare.degreeTree62_925All`, `OAI.UniversalTensorSquare.degreeTree62_956All`, `OAI.UniversalTensorSquare.degreeTree62_958All`, `OAI.UniversalTensorSquare.degreeTree62_964All`, `OAI.UniversalTensorSquare.degreeTree62_967All`, `OAI.UniversalTensorSquare.sg20509`, `OAI.UniversalTensorSquare.sg20758`, `OAI.UniversalTensorSquare.sg32394`, `OAI.UniversalTensorSquare.sg32434`, `OAI.UniversalTensorSquare.sg32498`, `OAI.UniversalTensorSquare.sg32535`, `OAI.UniversalTensorSquare.sg32542`, `OAI.UniversalTensorSquare.sg32567`, `OAI.UniversalTensorSquare.sg32580`, `OAI.UniversalTensorSquare.sg32609`, `OAI.UniversalTensorSquare.sg32616`, `OAI.UniversalTensorSquare.sg32634`, `OAI.UniversalTensorSquare.sg32640`, `OAI.UniversalTensorSquare.sg32651`, `OAI.UniversalTensorSquare.sg32670`, `OAI.UniversalTensorSquare.sg32693`, `OAI.UniversalTensorSquare.sg33210`, `OAI.UniversalTensorSquare.sg33493`, `OAI.UniversalTensorSquare.sg33539`, `OAI.UniversalTensorSquare.sg33568`, `OAI.UniversalTensorSquare.sg33596`, `OAI.UniversalTensorSquare.sg33746`, `OAI.UniversalTensorSquare.sg33829`, `OAI.UniversalTensorSquare.sg33959`, `OAI.UniversalTensorSquare.sg33984`, `OAI.UniversalTensorSquare.sg33989`, `OAI.UniversalTensorSquare.sg34082`, `OAI.UniversalTensorSquare.sg34561`, `OAI.UniversalTensorSquare.sg34790`, `OAI.UniversalTensorSquare.sg34835`, `OAI.UniversalTensorSquare.sg35005`, `OAI.UniversalTensorSquare.sg35119`, `OAI.UniversalTensorSquare.sg35137`, `OAI.UniversalTensorSquare.sg35144`, `OAI.UniversalTensorSquare.sg35181`, `OAI.UniversalTensorSquare.sg35322`, `OAI.UniversalTensorSquare.sg35399`, `OAI.UniversalTensorSquare.sg35463`, `OAI.UniversalTensorSquare.sg38062`, `OAI.UniversalTensorSquare.sg38384`, `OAI.UniversalTensorSquare.sg38402`, `OAI.UniversalTensorSquare.sg38988`, `OAI.UniversalTensorSquare.sg39057`, `OAI.UniversalTensorSquare.sg39184`, `OAI.UniversalTensorSquare.sg39200`, `OAI.UniversalTensorSquare.sg39545`, `OAI.UniversalTensorSquare.sg39998`, `OAI.UniversalTensorSquare.sg40073`, `OAI.UniversalTensorSquare.sg40947`, `OAI.UniversalTensorSquare.sg41542`, `OAI.UniversalTensorSquare.sg4161`, `OAI.UniversalTensorSquare.sg41650`, `OAI.UniversalTensorSquare.sg41851` and `OAI.UniversalTensorSquare.sg42368` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg238)

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

lemma sg238 : RowSquare [2,1,1,1,1,1,1] [8] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
