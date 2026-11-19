-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg3726
-- name    : OAI.UniversalTensorSquare.sg3726
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T14:16:10.271039+00:00
-- url     : https://prove2.me/theorems/453d4d0b-732c-4522-9d6a-c02ad147a91b
-- title:
--   OAI.UniversalTensorSquare.sg3726: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg3726` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes8.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes8.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg3726 : RowSquare [9,3,2,1] [3,3,3,3,3]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_157All`, `OAI.UniversalTensorSquare.sg15774`, `OAI.UniversalTensorSquare.sg31986`, `OAI.UniversalTensorSquare.sg33115`, `OAI.UniversalTensorSquare.sg33117`, `OAI.UniversalTensorSquare.sg33163`, `OAI.UniversalTensorSquare.sg33165`, `OAI.UniversalTensorSquare.sg33166`, `OAI.UniversalTensorSquare.sg34245`, `OAI.UniversalTensorSquare.sg34250`, `OAI.UniversalTensorSquare.sg34256`, `OAI.UniversalTensorSquare.sg34530`, `OAI.UniversalTensorSquare.sg34902`, `OAI.UniversalTensorSquare.sg34903`, `OAI.UniversalTensorSquare.sg35017`, `OAI.UniversalTensorSquare.sg35018`, `OAI.UniversalTensorSquare.sg35058`, `OAI.UniversalTensorSquare.sg35148`, `OAI.UniversalTensorSquare.sg35149`, `OAI.UniversalTensorSquare.sg35183`, `OAI.UniversalTensorSquare.sg35226`, `OAI.UniversalTensorSquare.sg35242`, `OAI.UniversalTensorSquare.sg35298`, `OAI.UniversalTensorSquare.sg37635`, `OAI.UniversalTensorSquare.sg37637`, `OAI.UniversalTensorSquare.sg37664`, `OAI.UniversalTensorSquare.sg37669`, `OAI.UniversalTensorSquare.sg37671`, `OAI.UniversalTensorSquare.sg38863`, `OAI.UniversalTensorSquare.sg38894`, `OAI.UniversalTensorSquare.sg39511`, `OAI.UniversalTensorSquare.sg39834`, `OAI.UniversalTensorSquare.sg39866`, `OAI.UniversalTensorSquare.sg39951`, `OAI.UniversalTensorSquare.sg39970`, `OAI.UniversalTensorSquare.sg39972`, `OAI.UniversalTensorSquare.sg41477`, `OAI.UniversalTensorSquare.sg41490`, `OAI.UniversalTensorSquare.sg41492`, `OAI.UniversalTensorSquare.sg42064` and `OAI.UniversalTensorSquare.sg42074` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes8.lean (declaration OAI.UniversalTensorSquare.sg3726)

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

lemma sg3726 : RowSquare [9,3,2,1] [3,3,3,3,3] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
