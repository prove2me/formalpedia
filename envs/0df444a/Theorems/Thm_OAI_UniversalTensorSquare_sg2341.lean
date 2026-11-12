-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2341
-- name    : OAI.UniversalTensorSquare.sg2341
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T00:49:33.307983+00:00
-- url     : https://prove2.me/theorems/4b5ee8d5-8b08-4e88-a82a-5a0a329cec48
-- title:
--   OAI.UniversalTensorSquare.sg2341: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2341` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2341 : RowSquare [7,4,2] [3,3,3,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_22All`, `OAI.UniversalTensorSquare.degreeTree62_255All`, `OAI.UniversalTensorSquare.degreeTree62_256All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_271All`, `OAI.UniversalTensorSquare.degreeTree62_274All`, `OAI.UniversalTensorSquare.degreeTree62_465All`, `OAI.UniversalTensorSquare.degreeTree62_659All`, `OAI.UniversalTensorSquare.degreeTree62_690All`, `OAI.UniversalTensorSquare.degreeTree62_692All`, `OAI.UniversalTensorSquare.sg17688`, `OAI.UniversalTensorSquare.sg34630`, `OAI.UniversalTensorSquare.sg34739`, `OAI.UniversalTensorSquare.sg34758`, `OAI.UniversalTensorSquare.sg34840`, `OAI.UniversalTensorSquare.sg34842`, `OAI.UniversalTensorSquare.sg34847`, `OAI.UniversalTensorSquare.sg34882`, `OAI.UniversalTensorSquare.sg34999`, `OAI.UniversalTensorSquare.sg35033`, `OAI.UniversalTensorSquare.sg37158`, `OAI.UniversalTensorSquare.sg38535`, `OAI.UniversalTensorSquare.sg38542`, `OAI.UniversalTensorSquare.sg39244`, `OAI.UniversalTensorSquare.sg39666`, `OAI.UniversalTensorSquare.sg39702`, `OAI.UniversalTensorSquare.sg41285`, `OAI.UniversalTensorSquare.sg41907`, `OAI.UniversalTensorSquare.sg41925`, `OAI.UniversalTensorSquare.sg41934` and `OAI.UniversalTensorSquare.sg42412` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean (declaration OAI.UniversalTensorSquare.sg2341)

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

lemma sg2341 : RowSquare [7,4,2] [3,3,3,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
