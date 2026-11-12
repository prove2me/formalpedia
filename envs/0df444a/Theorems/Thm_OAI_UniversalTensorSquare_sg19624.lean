-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg19624
-- name    : OAI.UniversalTensorSquare.sg19624
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:47:59.149765+00:00
-- url     : https://prove2.me/theorems/59319a4e-47e2-403e-918a-c210a4cdb6e6
-- title:
--   OAI.UniversalTensorSquare.sg19624: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg19624` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes47.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes47.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg19624 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,3,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_195All`, `OAI.UniversalTensorSquare.degreeTree62_438All`, `OAI.UniversalTensorSquare.degreeTree62_439All`, `OAI.UniversalTensorSquare.degreeTree62_444All`, `OAI.UniversalTensorSquare.sg33722`, `OAI.UniversalTensorSquare.sg33821`, `OAI.UniversalTensorSquare.sg33848`, `OAI.UniversalTensorSquare.sg33863`, `OAI.UniversalTensorSquare.sg33895`, `OAI.UniversalTensorSquare.sg34100`, `OAI.UniversalTensorSquare.sg34127`, `OAI.UniversalTensorSquare.sg34142`, `OAI.UniversalTensorSquare.sg34174`, `OAI.UniversalTensorSquare.sg34219`, `OAI.UniversalTensorSquare.sg34333`, `OAI.UniversalTensorSquare.sg34342`, `OAI.UniversalTensorSquare.sg34368`, `OAI.UniversalTensorSquare.sg34399`, `OAI.UniversalTensorSquare.sg34514`, `OAI.UniversalTensorSquare.sg34539`, `OAI.UniversalTensorSquare.sg36530`, `OAI.UniversalTensorSquare.sg36587`, `OAI.UniversalTensorSquare.sg36690`, `OAI.UniversalTensorSquare.sg36749`, `OAI.UniversalTensorSquare.sg36770`, `OAI.UniversalTensorSquare.sg36807`, `OAI.UniversalTensorSquare.sg36826` and `OAI.UniversalTensorSquare.sg36933` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes47.lean (declaration OAI.UniversalTensorSquare.sg19624)

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

lemma sg19624 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,3,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
