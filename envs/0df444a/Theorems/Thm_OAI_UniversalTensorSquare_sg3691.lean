-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3691
-- name    : OAI.UniversalTensorSquare.sg3691
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T13:49:20.980078+00:00
-- url     : https://prove2.me/theorems/d052cff9-c5b5-44a5-b311-f410e258e06b
-- title:
--   OAI.UniversalTensorSquare.sg3691: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3691` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3691 : RowSquare [9,2,2,1,1] [3,3,3,3,3]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.sg14433`, `OAI.UniversalTensorSquare.sg16662`, `OAI.UniversalTensorSquare.sg16667`, `OAI.UniversalTensorSquare.sg31991`, `OAI.UniversalTensorSquare.sg32286`, `OAI.UniversalTensorSquare.sg32289`, `OAI.UniversalTensorSquare.sg33640`, `OAI.UniversalTensorSquare.sg33648`, `OAI.UniversalTensorSquare.sg33650`, `OAI.UniversalTensorSquare.sg33984`, `OAI.UniversalTensorSquare.sg34248`, `OAI.UniversalTensorSquare.sg34252`, `OAI.UniversalTensorSquare.sg34254`, `OAI.UniversalTensorSquare.sg34536`, `OAI.UniversalTensorSquare.sg35329`, `OAI.UniversalTensorSquare.sg35331`, `OAI.UniversalTensorSquare.sg35378`, `OAI.UniversalTensorSquare.sg35455`, `OAI.UniversalTensorSquare.sg37010`, `OAI.UniversalTensorSquare.sg37693`, `OAI.UniversalTensorSquare.sg37695`, `OAI.UniversalTensorSquare.sg37696`, `OAI.UniversalTensorSquare.sg38908`, `OAI.UniversalTensorSquare.sg38911`, `OAI.UniversalTensorSquare.sg39981`, `OAI.UniversalTensorSquare.sg39985`, `OAI.UniversalTensorSquare.sg40748`, `OAI.UniversalTensorSquare.sg41500` and `OAI.UniversalTensorSquare.sg42087` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes7.lean (declaration OAI.UniversalTensorSquare.sg3691)

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

lemma sg3691 : RowSquare [9,2,2,1,1] [3,3,3,3,3] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
