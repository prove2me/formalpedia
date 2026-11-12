-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg228
-- name    : OAI.UniversalTensorSquare.sg228
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T22:56:59.254246+00:00
-- url     : https://prove2.me/theorems/f67039a5-c311-49bc-9b44-217db3b14a6c
-- title:
--   OAI.UniversalTensorSquare.sg228: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg228` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg228 : RowSquare [5,2] [3,3,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_554All`, `OAI.UniversalTensorSquare.degreeTree62_640All`, `OAI.UniversalTensorSquare.degreeTree62_654All`, `OAI.UniversalTensorSquare.degreeTree62_685All`, `OAI.UniversalTensorSquare.degreeTree62_693All`, `OAI.UniversalTensorSquare.degreeTree62_705All`, `OAI.UniversalTensorSquare.degreeTree62_706All`, `OAI.UniversalTensorSquare.sg18846`, `OAI.UniversalTensorSquare.sg19130`, `OAI.UniversalTensorSquare.sg19171`, `OAI.UniversalTensorSquare.sg20170`, `OAI.UniversalTensorSquare.sg31048`, `OAI.UniversalTensorSquare.sg31345`, `OAI.UniversalTensorSquare.sg31913`, `OAI.UniversalTensorSquare.sg33697`, `OAI.UniversalTensorSquare.sg33701`, `OAI.UniversalTensorSquare.sg33704`, `OAI.UniversalTensorSquare.sg33706`, `OAI.UniversalTensorSquare.sg37822`, `OAI.UniversalTensorSquare.sg38024`, `OAI.UniversalTensorSquare.sg38118`, `OAI.UniversalTensorSquare.sg38119`, `OAI.UniversalTensorSquare.sg38121`, `OAI.UniversalTensorSquare.sg38122`, `OAI.UniversalTensorSquare.sg38126`, `OAI.UniversalTensorSquare.sg39543`, `OAI.UniversalTensorSquare.sg39584`, `OAI.UniversalTensorSquare.sg40061`, `OAI.UniversalTensorSquare.sg40063`, `OAI.UniversalTensorSquare.sg40064`, `OAI.UniversalTensorSquare.sg40076`, `OAI.UniversalTensorSquare.sg40078`, `OAI.UniversalTensorSquare.sg40079`, `OAI.UniversalTensorSquare.sg40114`, `OAI.UniversalTensorSquare.sg41752`, `OAI.UniversalTensorSquare.sg42120`, `OAI.UniversalTensorSquare.sg42126`, `OAI.UniversalTensorSquare.sg42142`, `OAI.UniversalTensorSquare.sg42143`, `OAI.UniversalTensorSquare.sg42145`, `OAI.UniversalTensorSquare.sg42273`, `OAI.UniversalTensorSquare.sg42280`, `OAI.UniversalTensorSquare.sg42294`, `OAI.UniversalTensorSquare.sg42403`, `OAI.UniversalTensorSquare.sg42418`, `OAI.UniversalTensorSquare.sg42420`, `OAI.UniversalTensorSquare.sg42427`, `OAI.UniversalTensorSquare.sg42434`, `OAI.UniversalTensorSquare.sg42436`, `OAI.UniversalTensorSquare.sg42458`, `OAI.UniversalTensorSquare.sg42490`, `OAI.UniversalTensorSquare.sg42584`, `OAI.UniversalTensorSquare.sg42716`, `OAI.UniversalTensorSquare.sg42725` and `OAI.UniversalTensorSquare.sg6522` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg228)

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

lemma sg228 : RowSquare [5,2] [3,3,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
