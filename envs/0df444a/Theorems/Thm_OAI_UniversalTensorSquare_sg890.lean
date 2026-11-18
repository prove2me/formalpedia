-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg890
-- name    : OAI.UniversalTensorSquare.sg890
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:55:53.341266+00:00
-- url     : https://prove2.me/theorems/9712ddde-7771-40f5-9d1a-b966fbab1f63
-- title:
--   OAI.UniversalTensorSquare.sg890: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg890` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg890 : RowSquare [5,1,1,1,1,1] [2,2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_28All`, `OAI.UniversalTensorSquare.degreeTree62_604All`, `OAI.UniversalTensorSquare.sg10094`, `OAI.UniversalTensorSquare.sg10214`, `OAI.UniversalTensorSquare.sg10222`, `OAI.UniversalTensorSquare.sg10224`, `OAI.UniversalTensorSquare.sg10226`, `OAI.UniversalTensorSquare.sg10293`, `OAI.UniversalTensorSquare.sg10491`, `OAI.UniversalTensorSquare.sg11497`, `OAI.UniversalTensorSquare.sg12705`, `OAI.UniversalTensorSquare.sg1335`, `OAI.UniversalTensorSquare.sg14762`, `OAI.UniversalTensorSquare.sg17195`, `OAI.UniversalTensorSquare.sg17327`, `OAI.UniversalTensorSquare.sg20515`, `OAI.UniversalTensorSquare.sg20749`, `OAI.UniversalTensorSquare.sg20846`, `OAI.UniversalTensorSquare.sg21994`, `OAI.UniversalTensorSquare.sg21995`, `OAI.UniversalTensorSquare.sg22049`, `OAI.UniversalTensorSquare.sg22059`, `OAI.UniversalTensorSquare.sg22412`, `OAI.UniversalTensorSquare.sg24281`, `OAI.UniversalTensorSquare.sg24290`, `OAI.UniversalTensorSquare.sg24385`, `OAI.UniversalTensorSquare.sg25169`, `OAI.UniversalTensorSquare.sg25803`, `OAI.UniversalTensorSquare.sg26084`, `OAI.UniversalTensorSquare.sg26158`, `OAI.UniversalTensorSquare.sg26477`, `OAI.UniversalTensorSquare.sg26698`, `OAI.UniversalTensorSquare.sg26849`, `OAI.UniversalTensorSquare.sg26875`, `OAI.UniversalTensorSquare.sg27783`, `OAI.UniversalTensorSquare.sg28022`, `OAI.UniversalTensorSquare.sg28896`, `OAI.UniversalTensorSquare.sg28943`, `OAI.UniversalTensorSquare.sg29057`, `OAI.UniversalTensorSquare.sg29700`, `OAI.UniversalTensorSquare.sg32297`, `OAI.UniversalTensorSquare.sg32299`, `OAI.UniversalTensorSquare.sg32315`, `OAI.UniversalTensorSquare.sg32319`, `OAI.UniversalTensorSquare.sg32321`, `OAI.UniversalTensorSquare.sg32471`, `OAI.UniversalTensorSquare.sg32472`, `OAI.UniversalTensorSquare.sg32910`, `OAI.UniversalTensorSquare.sg3554`, `OAI.UniversalTensorSquare.sg36002`, `OAI.UniversalTensorSquare.sg36012`, `OAI.UniversalTensorSquare.sg36014`, `OAI.UniversalTensorSquare.sg36016`, `OAI.UniversalTensorSquare.sg36116`, `OAI.UniversalTensorSquare.sg36671`, `OAI.UniversalTensorSquare.sg36681`, `OAI.UniversalTensorSquare.sg36683`, `OAI.UniversalTensorSquare.sg36685`, `OAI.UniversalTensorSquare.sg36804`, `OAI.UniversalTensorSquare.sg37219`, `OAI.UniversalTensorSquare.sg37222`, `OAI.UniversalTensorSquare.sg37385`, `OAI.UniversalTensorSquare.sg38688`, `OAI.UniversalTensorSquare.sg4025`, `OAI.UniversalTensorSquare.sg41729`, `OAI.UniversalTensorSquare.sg41940`, `OAI.UniversalTensorSquare.sg4197`, `OAI.UniversalTensorSquare.sg42282`, `OAI.UniversalTensorSquare.sg4377`, `OAI.UniversalTensorSquare.sg4467` and `OAI.UniversalTensorSquare.sg7310` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves4.lean (declaration OAI.UniversalTensorSquare.sg890)

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

lemma sg890 : RowSquare [5,1,1,1,1,1] [2,2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
