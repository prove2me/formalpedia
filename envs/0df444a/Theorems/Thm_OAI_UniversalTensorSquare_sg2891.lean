-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg2891
-- name    : OAI.UniversalTensorSquare.sg2891
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T08:19:40.987198+00:00
-- url     : https://prove2.me/theorems/5008c8f3-f7be-4310-89c1-63fbe55264c7
-- title:
--   OAI.UniversalTensorSquare.sg2891: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg2891` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg2891 : RowSquare [8,2,1,1,1,1] [3,3,3,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_195All`, `OAI.UniversalTensorSquare.degreeTree62_199All`, `OAI.UniversalTensorSquare.degreeTree62_290All`, `OAI.UniversalTensorSquare.degreeTree62_476All`, `OAI.UniversalTensorSquare.degreeTree62_690All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_738All`, `OAI.UniversalTensorSquare.degreeTree62_923All`, `OAI.UniversalTensorSquare.degreeTree62_942All`, `OAI.UniversalTensorSquare.degreeTree62_946All`, `OAI.UniversalTensorSquare.degreeTree62_953All`, `OAI.UniversalTensorSquare.sg33396`, `OAI.UniversalTensorSquare.sg35232`, `OAI.UniversalTensorSquare.sg37270`, `OAI.UniversalTensorSquare.sg37273`, `OAI.UniversalTensorSquare.sg37276`, `OAI.UniversalTensorSquare.sg37278`, `OAI.UniversalTensorSquare.sg38027`, `OAI.UniversalTensorSquare.sg38029`, `OAI.UniversalTensorSquare.sg38441`, `OAI.UniversalTensorSquare.sg38567`, `OAI.UniversalTensorSquare.sg38568`, `OAI.UniversalTensorSquare.sg38570`, `OAI.UniversalTensorSquare.sg38571`, `OAI.UniversalTensorSquare.sg38573`, `OAI.UniversalTensorSquare.sg39235`, `OAI.UniversalTensorSquare.sg39603`, `OAI.UniversalTensorSquare.sg39606`, `OAI.UniversalTensorSquare.sg40094`, `OAI.UniversalTensorSquare.sg41883`, `OAI.UniversalTensorSquare.sg41884`, `OAI.UniversalTensorSquare.sg41886` and `OAI.UniversalTensorSquare.sg42017` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes5.lean (declaration OAI.UniversalTensorSquare.sg2891)

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

lemma sg2891 : RowSquare [8,2,1,1,1,1] [3,3,3,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
