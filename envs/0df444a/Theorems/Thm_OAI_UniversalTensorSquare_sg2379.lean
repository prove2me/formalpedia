-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2379
-- name    : OAI.UniversalTensorSquare.sg2379
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T01:28:16.147197+00:00
-- url     : https://prove2.me/theorems/7984dd9b-0e2b-4af9-95b7-8f4c84ed11d7
-- title:
--   OAI.UniversalTensorSquare.sg2379: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2379` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2379 : RowSquare [8,2,1,1,1] [4,3,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_716All`, `OAI.UniversalTensorSquare.sg36928`, `OAI.UniversalTensorSquare.sg36930`, `OAI.UniversalTensorSquare.sg38221`, `OAI.UniversalTensorSquare.sg38797`, `OAI.UniversalTensorSquare.sg38798`, `OAI.UniversalTensorSquare.sg38800`, `OAI.UniversalTensorSquare.sg38801`, `OAI.UniversalTensorSquare.sg38803`, `OAI.UniversalTensorSquare.sg38816`, `OAI.UniversalTensorSquare.sg38817`, `OAI.UniversalTensorSquare.sg38840`, `OAI.UniversalTensorSquare.sg39919`, `OAI.UniversalTensorSquare.sg39936`, `OAI.UniversalTensorSquare.sg39937` and `OAI.UniversalTensorSquare.sg42530` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes4.lean (declaration OAI.UniversalTensorSquare.sg2379)

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

lemma sg2379 : RowSquare [8,2,1,1,1] [4,3,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
