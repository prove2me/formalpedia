-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20710
-- name    : OAI.UniversalTensorSquare.sg20710
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:55:17.384503+00:00
-- url     : https://prove2.me/theorems/2562164a-b60a-4be3-b2f6-5671b7a29d51
-- title:
--   OAI.UniversalTensorSquare.sg20710: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20710` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20710 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,2,2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_1019All`, `OAI.UniversalTensorSquare.degreeTree62_620All`, `OAI.UniversalTensorSquare.degreeTree62_621All`, `OAI.UniversalTensorSquare.degreeTree62_625All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_719All`, `OAI.UniversalTensorSquare.degreeTree62_843All`, `OAI.UniversalTensorSquare.degreeTree62_930All`, `OAI.UniversalTensorSquare.degreeTree62_986All`, `OAI.UniversalTensorSquare.sg32862`, `OAI.UniversalTensorSquare.sg32992`, `OAI.UniversalTensorSquare.sg33032`, `OAI.UniversalTensorSquare.sg33065`, `OAI.UniversalTensorSquare.sg37062`, `OAI.UniversalTensorSquare.sg38333`, `OAI.UniversalTensorSquare.sg38370`, `OAI.UniversalTensorSquare.sg38911`, `OAI.UniversalTensorSquare.sg39524`, `OAI.UniversalTensorSquare.sg39942`, `OAI.UniversalTensorSquare.sg39971`, `OAI.UniversalTensorSquare.sg41161`, `OAI.UniversalTensorSquare.sg41828`, `OAI.UniversalTensorSquare.sg41840`, `OAI.UniversalTensorSquare.sg42070`, `OAI.UniversalTensorSquare.sg42077`, `OAI.UniversalTensorSquare.sg42082`, `OAI.UniversalTensorSquare.sg42341`, `OAI.UniversalTensorSquare.sg42351`, `OAI.UniversalTensorSquare.sg42358`, `OAI.UniversalTensorSquare.sg42537` and `OAI.UniversalTensorSquare.sg42542` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes50.lean (declaration OAI.UniversalTensorSquare.sg20710)

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

lemma sg20710 : RowSquare [9,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,2,2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
