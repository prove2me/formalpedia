-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3501
-- name    : OAI.UniversalTensorSquare.sg3501
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:31:55.882548+00:00
-- url     : https://prove2.me/theorems/a22adc92-f626-4c9b-8d80-20f00daf557b
-- title:
--   OAI.UniversalTensorSquare.sg3501: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3501` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3501 : RowSquare [7,4,3,1] [2,2,2,2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_259All`, `OAI.UniversalTensorSquare.degreeTree62_273All`, `OAI.UniversalTensorSquare.degreeTree62_285All`, `OAI.UniversalTensorSquare.sg14319`, `OAI.UniversalTensorSquare.sg34348`, `OAI.UniversalTensorSquare.sg34435`, `OAI.UniversalTensorSquare.sg34518`, `OAI.UniversalTensorSquare.sg34527`, `OAI.UniversalTensorSquare.sg34573`, `OAI.UniversalTensorSquare.sg34589`, `OAI.UniversalTensorSquare.sg35016`, `OAI.UniversalTensorSquare.sg35055`, `OAI.UniversalTensorSquare.sg35081`, `OAI.UniversalTensorSquare.sg35180`, `OAI.UniversalTensorSquare.sg35201`, `OAI.UniversalTensorSquare.sg35206`, `OAI.UniversalTensorSquare.sg35226`, `OAI.UniversalTensorSquare.sg35242`, `OAI.UniversalTensorSquare.sg35316`, `OAI.UniversalTensorSquare.sg35321` and `OAI.UniversalTensorSquare.sg35428` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3501)

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

lemma sg3501 : RowSquare [7,4,3,1] [2,2,2,2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
