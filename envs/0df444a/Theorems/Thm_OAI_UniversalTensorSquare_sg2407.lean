-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2407
-- name    : OAI.UniversalTensorSquare.sg2407
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T01:42:34.864562+00:00
-- url     : https://prove2.me/theorems/80f94fa7-b686-45b9-b9fb-b5090d997eb3
-- title:
--   OAI.UniversalTensorSquare.sg2407: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2407` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2407 : RowSquare [8,3,1,1] [3,3,3,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_256All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_261All`, `OAI.UniversalTensorSquare.degreeTree62_266All`, `OAI.UniversalTensorSquare.degreeTree62_27All`, `OAI.UniversalTensorSquare.degreeTree62_285All`, `OAI.UniversalTensorSquare.degreeTree62_288All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_302All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_476All`, `OAI.UniversalTensorSquare.degreeTree62_487All`, `OAI.UniversalTensorSquare.degreeTree62_490All`, `OAI.UniversalTensorSquare.degreeTree62_589All`, `OAI.UniversalTensorSquare.degreeTree62_593All`, `OAI.UniversalTensorSquare.degreeTree62_602All`, `OAI.UniversalTensorSquare.degreeTree62_610All`, `OAI.UniversalTensorSquare.degreeTree62_664All`, `OAI.UniversalTensorSquare.degreeTree62_685All`, `OAI.UniversalTensorSquare.degreeTree62_690All`, `OAI.UniversalTensorSquare.degreeTree62_692All`, `OAI.UniversalTensorSquare.degreeTree62_694All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_844All`, `OAI.UniversalTensorSquare.degreeTree62_847All`, `OAI.UniversalTensorSquare.degreeTree62_943All`, `OAI.UniversalTensorSquare.degreeTree62_953All`, `OAI.UniversalTensorSquare.sg16786`, `OAI.UniversalTensorSquare.sg17341`, `OAI.UniversalTensorSquare.sg18195`, `OAI.UniversalTensorSquare.sg19117`, `OAI.UniversalTensorSquare.sg19723`, `OAI.UniversalTensorSquare.sg32346`, `OAI.UniversalTensorSquare.sg33324`, `OAI.UniversalTensorSquare.sg33331`, `OAI.UniversalTensorSquare.sg34043`, `OAI.UniversalTensorSquare.sg35217`, `OAI.UniversalTensorSquare.sg35350`, `OAI.UniversalTensorSquare.sg35362`, `OAI.UniversalTensorSquare.sg35365`, `OAI.UniversalTensorSquare.sg37441`, `OAI.UniversalTensorSquare.sg37443`, `OAI.UniversalTensorSquare.sg37484`, `OAI.UniversalTensorSquare.sg37486`, `OAI.UniversalTensorSquare.sg38172`, `OAI.UniversalTensorSquare.sg38515`, `OAI.UniversalTensorSquare.sg38749`, `OAI.UniversalTensorSquare.sg39601`, `OAI.UniversalTensorSquare.sg41409` and `OAI.UniversalTensorSquare.sg42295` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean (declaration OAI.UniversalTensorSquare.sg2407)

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

lemma sg2407 : RowSquare [8,3,1,1] [3,3,3,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
