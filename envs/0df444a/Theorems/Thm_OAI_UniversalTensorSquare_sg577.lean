-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg577
-- name    : OAI.UniversalTensorSquare.sg577
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:46:35.604821+00:00
-- url     : https://prove2.me/theorems/8d3829c5-4b92-49b3-b918-909e8ad1f789
-- title:
--   OAI.UniversalTensorSquare.sg577: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg577` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg577 : RowSquare [4,3,2] [2,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_524All`, `OAI.UniversalTensorSquare.degreeTree62_527All`, `OAI.UniversalTensorSquare.degreeTree62_532All`, `OAI.UniversalTensorSquare.degreeTree62_550All`, `OAI.UniversalTensorSquare.degreeTree62_556All`, `OAI.UniversalTensorSquare.degreeTree62_584All`, `OAI.UniversalTensorSquare.degreeTree62_633All`, `OAI.UniversalTensorSquare.degreeTree62_656All`, `OAI.UniversalTensorSquare.degreeTree62_726All`, `OAI.UniversalTensorSquare.degreeTree62_733All`, `OAI.UniversalTensorSquare.degreeTree62_746All`, `OAI.UniversalTensorSquare.degreeTree62_829All`, `OAI.UniversalTensorSquare.degreeTree62_885All`, `OAI.UniversalTensorSquare.degreeTree62_941All`, `OAI.UniversalTensorSquare.degreeTree62_943All`, `OAI.UniversalTensorSquare.degreeTree62_958All`, `OAI.UniversalTensorSquare.degreeTree62_986All`, `OAI.UniversalTensorSquare.sg16586`, `OAI.UniversalTensorSquare.sg17843`, `OAI.UniversalTensorSquare.sg17921`, `OAI.UniversalTensorSquare.sg17946`, `OAI.UniversalTensorSquare.sg17948`, `OAI.UniversalTensorSquare.sg36404`, `OAI.UniversalTensorSquare.sg37846`, `OAI.UniversalTensorSquare.sg37913`, `OAI.UniversalTensorSquare.sg38982`, `OAI.UniversalTensorSquare.sg39053`, `OAI.UniversalTensorSquare.sg39054`, `OAI.UniversalTensorSquare.sg39100`, `OAI.UniversalTensorSquare.sg39102`, `OAI.UniversalTensorSquare.sg39225`, `OAI.UniversalTensorSquare.sg39264`, `OAI.UniversalTensorSquare.sg39471`, `OAI.UniversalTensorSquare.sg39499`, `OAI.UniversalTensorSquare.sg39559`, `OAI.UniversalTensorSquare.sg39630`, `OAI.UniversalTensorSquare.sg40051`, `OAI.UniversalTensorSquare.sg40090`, `OAI.UniversalTensorSquare.sg40122`, `OAI.UniversalTensorSquare.sg40130`, `OAI.UniversalTensorSquare.sg40150`, `OAI.UniversalTensorSquare.sg40169`, `OAI.UniversalTensorSquare.sg40176`, `OAI.UniversalTensorSquare.sg40217`, `OAI.UniversalTensorSquare.sg40218`, `OAI.UniversalTensorSquare.sg40866`, `OAI.UniversalTensorSquare.sg40903`, `OAI.UniversalTensorSquare.sg41122`, `OAI.UniversalTensorSquare.sg41577`, `OAI.UniversalTensorSquare.sg41635`, `OAI.UniversalTensorSquare.sg41727`, `OAI.UniversalTensorSquare.sg41739`, `OAI.UniversalTensorSquare.sg41787`, `OAI.UniversalTensorSquare.sg41887`, `OAI.UniversalTensorSquare.sg41992`, `OAI.UniversalTensorSquare.sg42007`, `OAI.UniversalTensorSquare.sg42135`, `OAI.UniversalTensorSquare.sg42175`, `OAI.UniversalTensorSquare.sg42237`, `OAI.UniversalTensorSquare.sg42265`, `OAI.UniversalTensorSquare.sg42299`, `OAI.UniversalTensorSquare.sg42421`, `OAI.UniversalTensorSquare.sg42446`, `OAI.UniversalTensorSquare.sg42485`, `OAI.UniversalTensorSquare.sg42572`, `OAI.UniversalTensorSquare.sg42610`, `OAI.UniversalTensorSquare.sg42653`, `OAI.UniversalTensorSquare.sg42665`, `OAI.UniversalTensorSquare.sg42692`, `OAI.UniversalTensorSquare.sg42711`, `OAI.UniversalTensorSquare.sg42719`, `OAI.UniversalTensorSquare.sg42734`, `OAI.UniversalTensorSquare.sg42749`, `OAI.UniversalTensorSquare.sg42761`, `OAI.UniversalTensorSquare.sg42903`, `OAI.UniversalTensorSquare.sg43055`, `OAI.UniversalTensorSquare.sg43074`, `OAI.UniversalTensorSquare.sg43128`, `OAI.UniversalTensorSquare.sg43134`, `OAI.UniversalTensorSquare.sg43217`, `OAI.UniversalTensorSquare.sg43220` and `OAI.UniversalTensorSquare.sg43224` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg577)

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

lemma sg577 : RowSquare [4,3,2] [2,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
