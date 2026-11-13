-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3008
-- name    : OAI.UniversalTensorSquare.sg3008
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T09:38:37.535175+00:00
-- url     : https://prove2.me/theorems/0404a9ef-65d5-41ac-aaf3-cf05e8ece8da
-- title:
--   OAI.UniversalTensorSquare.sg3008: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3008` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3008 : RowSquare [8,3,2,1] [3,3,3,3,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_110All`, `OAI.UniversalTensorSquare.degreeTree62_113All`, `OAI.UniversalTensorSquare.degreeTree62_114All`, `OAI.UniversalTensorSquare.degreeTree62_136All`, `OAI.UniversalTensorSquare.degreeTree62_137All`, `OAI.UniversalTensorSquare.degreeTree62_138All`, `OAI.UniversalTensorSquare.degreeTree62_225All`, `OAI.UniversalTensorSquare.degreeTree62_230All`, `OAI.UniversalTensorSquare.degreeTree62_235All`, `OAI.UniversalTensorSquare.degreeTree62_306All`, `OAI.UniversalTensorSquare.degreeTree62_317All`, `OAI.UniversalTensorSquare.degreeTree62_486All`, `OAI.UniversalTensorSquare.degreeTree62_49All`, `OAI.UniversalTensorSquare.degreeTree62_502All`, `OAI.UniversalTensorSquare.degreeTree62_55All`, `OAI.UniversalTensorSquare.sg17345`, `OAI.UniversalTensorSquare.sg32570`, `OAI.UniversalTensorSquare.sg32583`, `OAI.UniversalTensorSquare.sg32585`, `OAI.UniversalTensorSquare.sg32632`, `OAI.UniversalTensorSquare.sg33361`, `OAI.UniversalTensorSquare.sg33466`, `OAI.UniversalTensorSquare.sg33487`, `OAI.UniversalTensorSquare.sg33524`, `OAI.UniversalTensorSquare.sg33960`, `OAI.UniversalTensorSquare.sg34134`, `OAI.UniversalTensorSquare.sg34136`, `OAI.UniversalTensorSquare.sg34143`, `OAI.UniversalTensorSquare.sg34519`, `OAI.UniversalTensorSquare.sg34540`, `OAI.UniversalTensorSquare.sg35275`, `OAI.UniversalTensorSquare.sg35397`, `OAI.UniversalTensorSquare.sg35398`, `OAI.UniversalTensorSquare.sg35399`, `OAI.UniversalTensorSquare.sg35417`, `OAI.UniversalTensorSquare.sg35430`, `OAI.UniversalTensorSquare.sg37562`, `OAI.UniversalTensorSquare.sg39469`, `OAI.UniversalTensorSquare.sg39470`, `OAI.UniversalTensorSquare.sg39942`, `OAI.UniversalTensorSquare.sg40665` and `OAI.UniversalTensorSquare.sg42988` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes6.lean (declaration OAI.UniversalTensorSquare.sg3008)

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

lemma sg3008 : RowSquare [8,3,2,1] [3,3,3,3,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
