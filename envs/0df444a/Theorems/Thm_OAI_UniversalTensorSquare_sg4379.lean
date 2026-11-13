-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4379
-- name    : OAI.UniversalTensorSquare.sg4379
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T21:59:59.989499+00:00
-- url     : https://prove2.me/theorems/9d8cc0e6-b0c0-4fdc-8f87-4dc158ecb76c
-- title:
--   OAI.UniversalTensorSquare.sg4379: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4379` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4379 : RowSquare [8,3,2,1,1,1] [3,3,3,3,3,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_13All`, `OAI.UniversalTensorSquare.degreeTree62_389All`, `OAI.UniversalTensorSquare.degreeTree62_390All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.degreeTree62_73All`, `OAI.UniversalTensorSquare.degreeTree62_81All`, `OAI.UniversalTensorSquare.degreeTree62_96All`, `OAI.UniversalTensorSquare.sg19310`, `OAI.UniversalTensorSquare.sg20342`, `OAI.UniversalTensorSquare.sg20377`, `OAI.UniversalTensorSquare.sg31997`, `OAI.UniversalTensorSquare.sg32842`, `OAI.UniversalTensorSquare.sg32844`, `OAI.UniversalTensorSquare.sg32853`, `OAI.UniversalTensorSquare.sg32930`, `OAI.UniversalTensorSquare.sg32932`, `OAI.UniversalTensorSquare.sg32934`, `OAI.UniversalTensorSquare.sg32936`, `OAI.UniversalTensorSquare.sg33042`, `OAI.UniversalTensorSquare.sg33044`, `OAI.UniversalTensorSquare.sg33074`, `OAI.UniversalTensorSquare.sg33075`, `OAI.UniversalTensorSquare.sg33076`, `OAI.UniversalTensorSquare.sg33081`, `OAI.UniversalTensorSquare.sg33082`, `OAI.UniversalTensorSquare.sg33085`, `OAI.UniversalTensorSquare.sg36336` and `OAI.UniversalTensorSquare.sg39529` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean (declaration OAI.UniversalTensorSquare.sg4379)

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

lemma sg4379 : RowSquare [8,3,2,1,1,1] [3,3,3,3,3,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
