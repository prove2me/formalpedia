-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2374
-- name    : OAI.UniversalTensorSquare.sg2374
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T01:23:57.450201+00:00
-- url     : https://prove2.me/theorems/902a979a-a931-410d-bb29-9d943b2d7667
-- title:
--   OAI.UniversalTensorSquare.sg2374: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2374` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2374 : RowSquare [8,2,1,1,1] [3,3,3,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_110All`, `OAI.UniversalTensorSquare.degreeTree62_114All`, `OAI.UniversalTensorSquare.degreeTree62_117All`, `OAI.UniversalTensorSquare.degreeTree62_191All`, `OAI.UniversalTensorSquare.degreeTree62_193All`, `OAI.UniversalTensorSquare.degreeTree62_196All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_607All`, `OAI.UniversalTensorSquare.sg12566`, `OAI.UniversalTensorSquare.sg32347`, `OAI.UniversalTensorSquare.sg32348`, `OAI.UniversalTensorSquare.sg32350`, `OAI.UniversalTensorSquare.sg32351`, `OAI.UniversalTensorSquare.sg32353`, `OAI.UniversalTensorSquare.sg32355`, `OAI.UniversalTensorSquare.sg33329`, `OAI.UniversalTensorSquare.sg33330`, `OAI.UniversalTensorSquare.sg33332`, `OAI.UniversalTensorSquare.sg33333`, `OAI.UniversalTensorSquare.sg34159`, `OAI.UniversalTensorSquare.sg34310`, `OAI.UniversalTensorSquare.sg34311`, `OAI.UniversalTensorSquare.sg34313`, `OAI.UniversalTensorSquare.sg34314`, `OAI.UniversalTensorSquare.sg34316`, `OAI.UniversalTensorSquare.sg34318`, `OAI.UniversalTensorSquare.sg34393`, `OAI.UniversalTensorSquare.sg34395`, `OAI.UniversalTensorSquare.sg34399`, `OAI.UniversalTensorSquare.sg35367`, `OAI.UniversalTensorSquare.sg37370`, `OAI.UniversalTensorSquare.sg37372`, `OAI.UniversalTensorSquare.sg38156`, `OAI.UniversalTensorSquare.sg38158` and `OAI.UniversalTensorSquare.sg39366` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean (declaration OAI.UniversalTensorSquare.sg2374)

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

lemma sg2374 : RowSquare [8,2,1,1,1] [3,3,3,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
