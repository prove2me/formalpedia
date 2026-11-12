-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20511
-- name    : OAI.UniversalTensorSquare.sg20511
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:29.175026+00:00
-- url     : https://prove2.me/theorems/5a5cff38-2847-49e5-b9c5-01f916ecf9c8
-- title:
--   OAI.UniversalTensorSquare.sg20511: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20511` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20511 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2,2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_105All`, `OAI.UniversalTensorSquare.degreeTree62_114All`, `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_184All`, `OAI.UniversalTensorSquare.degreeTree62_196All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_217All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_232All`, `OAI.UniversalTensorSquare.degreeTree62_239All`, `OAI.UniversalTensorSquare.degreeTree62_23All`, `OAI.UniversalTensorSquare.degreeTree62_249All`, `OAI.UniversalTensorSquare.degreeTree62_255All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_262All`, `OAI.UniversalTensorSquare.degreeTree62_271All`, `OAI.UniversalTensorSquare.degreeTree62_274All`, `OAI.UniversalTensorSquare.degreeTree62_277All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_287All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_34All`, `OAI.UniversalTensorSquare.degreeTree62_357All`, `OAI.UniversalTensorSquare.degreeTree62_423All`, `OAI.UniversalTensorSquare.degreeTree62_456All`, `OAI.UniversalTensorSquare.degreeTree62_486All`, `OAI.UniversalTensorSquare.degreeTree62_577All`, `OAI.UniversalTensorSquare.degreeTree62_630All`, `OAI.UniversalTensorSquare.degreeTree62_650All`, `OAI.UniversalTensorSquare.sg32299`, `OAI.UniversalTensorSquare.sg32361`, `OAI.UniversalTensorSquare.sg32374`, `OAI.UniversalTensorSquare.sg32453`, `OAI.UniversalTensorSquare.sg33127`, `OAI.UniversalTensorSquare.sg33169`, `OAI.UniversalTensorSquare.sg33371`, `OAI.UniversalTensorSquare.sg33401`, `OAI.UniversalTensorSquare.sg33761`, `OAI.UniversalTensorSquare.sg34207`, `OAI.UniversalTensorSquare.sg34752`, `OAI.UniversalTensorSquare.sg34810`, `OAI.UniversalTensorSquare.sg34880`, `OAI.UniversalTensorSquare.sg34916`, `OAI.UniversalTensorSquare.sg34955`, `OAI.UniversalTensorSquare.sg34992`, `OAI.UniversalTensorSquare.sg35280`, `OAI.UniversalTensorSquare.sg35325`, `OAI.UniversalTensorSquare.sg36649`, `OAI.UniversalTensorSquare.sg37800`, `OAI.UniversalTensorSquare.sg37995`, `OAI.UniversalTensorSquare.sg38565`, `OAI.UniversalTensorSquare.sg38664` and `OAI.UniversalTensorSquare.sg39347` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20511)

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

lemma sg20511 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2,2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
