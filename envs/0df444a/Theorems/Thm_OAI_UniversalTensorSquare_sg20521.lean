-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20521
-- name    : OAI.UniversalTensorSquare.sg20521
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:45.400088+00:00
-- url     : https://prove2.me/theorems/d922e481-c704-42df-9f3c-0e6a19ac025d
-- title:
--   OAI.UniversalTensorSquare.sg20521: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20521` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20521 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_134All`, `OAI.UniversalTensorSquare.degreeTree62_138All`, `OAI.UniversalTensorSquare.degreeTree62_13All`, `OAI.UniversalTensorSquare.degreeTree62_173All`, `OAI.UniversalTensorSquare.degreeTree62_178All`, `OAI.UniversalTensorSquare.degreeTree62_20All`, `OAI.UniversalTensorSquare.degreeTree62_216All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_230All`, `OAI.UniversalTensorSquare.degreeTree62_233All`, `OAI.UniversalTensorSquare.degreeTree62_249All`, `OAI.UniversalTensorSquare.degreeTree62_25All`, `OAI.UniversalTensorSquare.degreeTree62_274All`, `OAI.UniversalTensorSquare.degreeTree62_279All`, `OAI.UniversalTensorSquare.degreeTree62_287All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_300All`, `OAI.UniversalTensorSquare.degreeTree62_306All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_309All`, `OAI.UniversalTensorSquare.degreeTree62_38All`, `OAI.UniversalTensorSquare.degreeTree62_39All`, `OAI.UniversalTensorSquare.degreeTree62_43All`, `OAI.UniversalTensorSquare.degreeTree62_47All`, `OAI.UniversalTensorSquare.degreeTree62_4All`, `OAI.UniversalTensorSquare.degreeTree62_55All`, `OAI.UniversalTensorSquare.degreeTree62_59All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.degreeTree62_73All`, `OAI.UniversalTensorSquare.sg32706`, `OAI.UniversalTensorSquare.sg32850`, `OAI.UniversalTensorSquare.sg33075`, `OAI.UniversalTensorSquare.sg33375`, `OAI.UniversalTensorSquare.sg33543`, `OAI.UniversalTensorSquare.sg33605`, `OAI.UniversalTensorSquare.sg34724`, `OAI.UniversalTensorSquare.sg34920`, `OAI.UniversalTensorSquare.sg37710` and `OAI.UniversalTensorSquare.sg40218` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20521)

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

lemma sg20521 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
