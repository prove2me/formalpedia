-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3620
-- name    : OAI.UniversalTensorSquare.sg3620
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T15:53:33.591792+00:00
-- url     : https://prove2.me/theorems/04e067f2-2346-44a1-83bc-69e99dfc1530
-- title:
--   OAI.UniversalTensorSquare.sg3620: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3620` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3620 : RowSquare [8,3,2,1,1] [3,3,3,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_182All`, `OAI.UniversalTensorSquare.degreeTree62_187All`, `OAI.UniversalTensorSquare.degreeTree62_201All`, `OAI.UniversalTensorSquare.degreeTree62_22All`, `OAI.UniversalTensorSquare.degreeTree62_23All`, `OAI.UniversalTensorSquare.degreeTree62_25All`, `OAI.UniversalTensorSquare.degreeTree62_367All`, `OAI.UniversalTensorSquare.degreeTree62_435All`, `OAI.UniversalTensorSquare.degreeTree62_479All`, `OAI.UniversalTensorSquare.degreeTree62_562All`, `OAI.UniversalTensorSquare.degreeTree62_602All`, `OAI.UniversalTensorSquare.degreeTree62_610All`, `OAI.UniversalTensorSquare.degreeTree62_614All`, `OAI.UniversalTensorSquare.degreeTree62_782All`, `OAI.UniversalTensorSquare.degreeTree62_786All`, `OAI.UniversalTensorSquare.degreeTree62_81All`, `OAI.UniversalTensorSquare.degreeTree62_821All`, `OAI.UniversalTensorSquare.degreeTree62_844All`, `OAI.UniversalTensorSquare.degreeTree62_851All`, `OAI.UniversalTensorSquare.degreeTree62_852All`, `OAI.UniversalTensorSquare.sg15613`, `OAI.UniversalTensorSquare.sg18291`, `OAI.UniversalTensorSquare.sg18294`, `OAI.UniversalTensorSquare.sg32339`, `OAI.UniversalTensorSquare.sg32340`, `OAI.UniversalTensorSquare.sg32341`, `OAI.UniversalTensorSquare.sg32398`, `OAI.UniversalTensorSquare.sg32446`, `OAI.UniversalTensorSquare.sg33088`, `OAI.UniversalTensorSquare.sg33095`, `OAI.UniversalTensorSquare.sg33151`, `OAI.UniversalTensorSquare.sg34076`, `OAI.UniversalTensorSquare.sg34077`, `OAI.UniversalTensorSquare.sg34078`, `OAI.UniversalTensorSquare.sg34276`, `OAI.UniversalTensorSquare.sg35055`, `OAI.UniversalTensorSquare.sg36101`, `OAI.UniversalTensorSquare.sg36841`, `OAI.UniversalTensorSquare.sg38051`, `OAI.UniversalTensorSquare.sg38768`, `OAI.UniversalTensorSquare.sg39374`, `OAI.UniversalTensorSquare.sg40631`, `OAI.UniversalTensorSquare.sg40633` and `OAI.UniversalTensorSquare.sg40650` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3620)

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

lemma sg3620 : RowSquare [8,3,2,1,1] [3,3,3,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
