-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg490
-- name    : OAI.UniversalTensorSquare.sg490
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:35:23.051472+00:00
-- url     : https://prove2.me/theorems/cc531c79-ec95-4dad-9ce0-1d7cc8ce47dd
-- title:
--   OAI.UniversalTensorSquare.sg490: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg490` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg490 : RowSquare [3,3,1,1,1] [2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree26_18All`, `OAI.UniversalTensorSquare.degreeTree26_41All`, `OAI.UniversalTensorSquare.sg13434`, `OAI.UniversalTensorSquare.sg18342`, `OAI.UniversalTensorSquare.sg34472`, `OAI.UniversalTensorSquare.sg34475`, `OAI.UniversalTensorSquare.sg34477`, `OAI.UniversalTensorSquare.sg36150`, `OAI.UniversalTensorSquare.sg36153`, `OAI.UniversalTensorSquare.sg36155`, `OAI.UniversalTensorSquare.sg40587`, `OAI.UniversalTensorSquare.sg40681`, `OAI.UniversalTensorSquare.sg40710`, `OAI.UniversalTensorSquare.sg40714`, `OAI.UniversalTensorSquare.sg40716`, `OAI.UniversalTensorSquare.sg41021`, `OAI.UniversalTensorSquare.sg41116`, `OAI.UniversalTensorSquare.sg41117`, `OAI.UniversalTensorSquare.sg41119`, `OAI.UniversalTensorSquare.sg41141`, `OAI.UniversalTensorSquare.sg41142`, `OAI.UniversalTensorSquare.sg41144`, `OAI.UniversalTensorSquare.sg41267`, `OAI.UniversalTensorSquare.sg41271`, `OAI.UniversalTensorSquare.sg41273`, `OAI.UniversalTensorSquare.sg41336`, `OAI.UniversalTensorSquare.sg41340`, `OAI.UniversalTensorSquare.sg41342`, `OAI.UniversalTensorSquare.sg41385`, `OAI.UniversalTensorSquare.sg41386`, `OAI.UniversalTensorSquare.sg41388`, `OAI.UniversalTensorSquare.sg41439`, `OAI.UniversalTensorSquare.sg41440`, `OAI.UniversalTensorSquare.sg41442`, `OAI.UniversalTensorSquare.sg41457`, `OAI.UniversalTensorSquare.sg41460`, `OAI.UniversalTensorSquare.sg42126`, `OAI.UniversalTensorSquare.sg42816`, `OAI.UniversalTensorSquare.sg42819`, `OAI.UniversalTensorSquare.sg42891`, `OAI.UniversalTensorSquare.sg42894`, `OAI.UniversalTensorSquare.sg42895`, `OAI.UniversalTensorSquare.sg42958`, `OAI.UniversalTensorSquare.sg42998`, `OAI.UniversalTensorSquare.sg42999`, `OAI.UniversalTensorSquare.sg43007`, `OAI.UniversalTensorSquare.sg43008`, `OAI.UniversalTensorSquare.sg43065`, `OAI.UniversalTensorSquare.sg43068`, `OAI.UniversalTensorSquare.sg43115`, `OAI.UniversalTensorSquare.sg43130` and `OAI.UniversalTensorSquare.sg43141` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg490)

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

lemma sg490 : RowSquare [3,3,1,1,1] [2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
