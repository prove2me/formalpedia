-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg942
-- name    : OAI.UniversalTensorSquare.sg942
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:01:50.562454+00:00
-- url     : https://prove2.me/theorems/219f55f2-44e2-4ebe-9314-e3ec4b359256
-- title:
--   OAI.UniversalTensorSquare.sg942: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg942` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg942 : RowSquare [5,2,2,1] [2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_616All`, `OAI.UniversalTensorSquare.degreeTree62_692All`, `OAI.UniversalTensorSquare.degreeTree62_694All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_937All`, `OAI.UniversalTensorSquare.degreeTree62_955All`, `OAI.UniversalTensorSquare.sg26100`, `OAI.UniversalTensorSquare.sg37608`, `OAI.UniversalTensorSquare.sg37609`, `OAI.UniversalTensorSquare.sg37643`, `OAI.UniversalTensorSquare.sg37644`, `OAI.UniversalTensorSquare.sg38856`, `OAI.UniversalTensorSquare.sg38879`, `OAI.UniversalTensorSquare.sg39684`, `OAI.UniversalTensorSquare.sg39688`, `OAI.UniversalTensorSquare.sg39888`, `OAI.UniversalTensorSquare.sg39891`, `OAI.UniversalTensorSquare.sg39892`, `OAI.UniversalTensorSquare.sg41265`, `OAI.UniversalTensorSquare.sg41279`, `OAI.UniversalTensorSquare.sg41281`, `OAI.UniversalTensorSquare.sg41334`, `OAI.UniversalTensorSquare.sg41348`, `OAI.UniversalTensorSquare.sg41350`, `OAI.UniversalTensorSquare.sg41356`, `OAI.UniversalTensorSquare.sg41365`, `OAI.UniversalTensorSquare.sg41367`, `OAI.UniversalTensorSquare.sg41441`, `OAI.UniversalTensorSquare.sg41443`, `OAI.UniversalTensorSquare.sg41791`, `OAI.UniversalTensorSquare.sg41800`, `OAI.UniversalTensorSquare.sg42163`, `OAI.UniversalTensorSquare.sg42254`, `OAI.UniversalTensorSquare.sg42601`, `OAI.UniversalTensorSquare.sg6640`, `OAI.UniversalTensorSquare.sg6649`, `OAI.UniversalTensorSquare.sg8011` and `OAI.UniversalTensorSquare.sg9108` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sg942)

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

lemma sg942 : RowSquare [5,2,2,1] [2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
