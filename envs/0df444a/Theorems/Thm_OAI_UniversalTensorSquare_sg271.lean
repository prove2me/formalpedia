-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg271
-- name    : OAI.UniversalTensorSquare.sg271
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T12:00:54.084195+00:00
-- url     : https://prove2.me/theorems/3ae4b44f-dfaa-4b66-9df8-e1bcb31ac27c
-- title:
--   OAI.UniversalTensorSquare.sg271: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg271` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg271 : RowSquare [3,2,1,1,1] [2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_120All`, `OAI.UniversalTensorSquare.degreeTree43_126All`, `OAI.UniversalTensorSquare.degreeTree43_197All`, `OAI.UniversalTensorSquare.degreeTree43_234All`, `OAI.UniversalTensorSquare.degreeTree43_236All`, `OAI.UniversalTensorSquare.degreeTree43_238All`, `OAI.UniversalTensorSquare.degreeTree43_257All`, `OAI.UniversalTensorSquare.degreeTree43_292All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_47All`, `OAI.UniversalTensorSquare.degreeTree43_57All`, `OAI.UniversalTensorSquare.degreeTree43_598All`, `OAI.UniversalTensorSquare.degreeTree43_601All`, `OAI.UniversalTensorSquare.degreeTree43_609All`, `OAI.UniversalTensorSquare.degreeTree43_635All`, `OAI.UniversalTensorSquare.degreeTree62_1004All`, `OAI.UniversalTensorSquare.degreeTree62_128All`, `OAI.UniversalTensorSquare.degreeTree62_159All`, `OAI.UniversalTensorSquare.degreeTree62_371All`, `OAI.UniversalTensorSquare.degreeTree62_404All`, `OAI.UniversalTensorSquare.degreeTree62_42All`, `OAI.UniversalTensorSquare.degreeTree62_467All`, `OAI.UniversalTensorSquare.degreeTree62_483All`, `OAI.UniversalTensorSquare.degreeTree62_503All`, `OAI.UniversalTensorSquare.degreeTree62_822All`, `OAI.UniversalTensorSquare.degreeTree62_823All`, `OAI.UniversalTensorSquare.sg20053`, `OAI.UniversalTensorSquare.sg21960`, `OAI.UniversalTensorSquare.sg22704`, `OAI.UniversalTensorSquare.sg23253`, `OAI.UniversalTensorSquare.sg24313`, `OAI.UniversalTensorSquare.sg24425`, `OAI.UniversalTensorSquare.sg24664`, `OAI.UniversalTensorSquare.sg24875`, `OAI.UniversalTensorSquare.sg24878`, `OAI.UniversalTensorSquare.sg24955`, `OAI.UniversalTensorSquare.sg25022`, `OAI.UniversalTensorSquare.sg25040`, `OAI.UniversalTensorSquare.sg25182`, `OAI.UniversalTensorSquare.sg25239`, `OAI.UniversalTensorSquare.sg25294`, `OAI.UniversalTensorSquare.sg25298`, `OAI.UniversalTensorSquare.sg25339`, `OAI.UniversalTensorSquare.sg26653`, `OAI.UniversalTensorSquare.sg26704`, `OAI.UniversalTensorSquare.sg33432`, `OAI.UniversalTensorSquare.sg36485`, `OAI.UniversalTensorSquare.sg37174`, `OAI.UniversalTensorSquare.sg37188`, `OAI.UniversalTensorSquare.sg37364`, `OAI.UniversalTensorSquare.sg37367`, `OAI.UniversalTensorSquare.sg37369` and `OAI.UniversalTensorSquare.sg931` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves1.lean (declaration OAI.UniversalTensorSquare.sg271)

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

lemma sg271 : RowSquare [3,2,1,1,1] [2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
