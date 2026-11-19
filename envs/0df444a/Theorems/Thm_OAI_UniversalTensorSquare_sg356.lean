-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg356
-- name    : OAI.UniversalTensorSquare.sg356
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T11:48:52.230193+00:00
-- url     : https://prove2.me/theorems/b5d03681-3c39-43fb-8957-6f54f4cdd1fc
-- title:
--   OAI.UniversalTensorSquare.sg356: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg356` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg356 : RowSquare [4,3,1] [2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_260All`, `OAI.UniversalTensorSquare.degreeTree43_42All`, `OAI.UniversalTensorSquare.degreeTree62_726All`, `OAI.UniversalTensorSquare.degreeTree62_883All`, `OAI.UniversalTensorSquare.degreeTree62_956All`, `OAI.UniversalTensorSquare.degreeTree62_958All`, `OAI.UniversalTensorSquare.degreeTree62_967All`, `OAI.UniversalTensorSquare.degreeTree62_974All`, `OAI.UniversalTensorSquare.sg15134`, `OAI.UniversalTensorSquare.sg15533`, `OAI.UniversalTensorSquare.sg18750`, `OAI.UniversalTensorSquare.sg23564`, `OAI.UniversalTensorSquare.sg23571`, `OAI.UniversalTensorSquare.sg23577`, `OAI.UniversalTensorSquare.sg24746`, `OAI.UniversalTensorSquare.sg24749`, `OAI.UniversalTensorSquare.sg27000`, `OAI.UniversalTensorSquare.sg27041`, `OAI.UniversalTensorSquare.sg27069`, `OAI.UniversalTensorSquare.sg27077`, `OAI.UniversalTensorSquare.sg27084`, `OAI.UniversalTensorSquare.sg29991`, `OAI.UniversalTensorSquare.sg30731`, `OAI.UniversalTensorSquare.sg31135`, `OAI.UniversalTensorSquare.sg31143`, `OAI.UniversalTensorSquare.sg31150`, `OAI.UniversalTensorSquare.sg39164`, `OAI.UniversalTensorSquare.sg40177`, `OAI.UniversalTensorSquare.sg40181`, `OAI.UniversalTensorSquare.sg40897`, `OAI.UniversalTensorSquare.sg40898`, `OAI.UniversalTensorSquare.sg40899`, `OAI.UniversalTensorSquare.sg41024`, `OAI.UniversalTensorSquare.sg41025`, `OAI.UniversalTensorSquare.sg41026`, `OAI.UniversalTensorSquare.sg41098`, `OAI.UniversalTensorSquare.sg41650`, `OAI.UniversalTensorSquare.sg41712`, `OAI.UniversalTensorSquare.sg41725`, `OAI.UniversalTensorSquare.sg41932`, `OAI.UniversalTensorSquare.sg41983`, `OAI.UniversalTensorSquare.sg42034`, `OAI.UniversalTensorSquare.sg42042`, `OAI.UniversalTensorSquare.sg42673`, `OAI.UniversalTensorSquare.sg42688`, `OAI.UniversalTensorSquare.sg42690`, `OAI.UniversalTensorSquare.sg42751` and `OAI.UniversalTensorSquare.sg4987` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves2.lean (declaration OAI.UniversalTensorSquare.sg356)

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

lemma sg356 : RowSquare [4,3,1] [2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
