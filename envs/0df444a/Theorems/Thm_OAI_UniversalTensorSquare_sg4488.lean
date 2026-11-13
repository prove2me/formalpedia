-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4488
-- name    : OAI.UniversalTensorSquare.sg4488
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:15:48.008202+00:00
-- url     : https://prove2.me/theorems/ad794e8b-6ce3-4b9b-8b4e-5e0b65b34ae6
-- title:
--   OAI.UniversalTensorSquare.sg4488: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4488` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4488 : RowSquare [9,3,2,1,1] [3,3,3,3,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_117All`, `OAI.UniversalTensorSquare.degreeTree62_11All`, `OAI.UniversalTensorSquare.degreeTree62_12All`, `OAI.UniversalTensorSquare.degreeTree62_290All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_32All`, `OAI.UniversalTensorSquare.degreeTree62_50All`, `OAI.UniversalTensorSquare.degreeTree62_65All`, `OAI.UniversalTensorSquare.degreeTree62_66All`, `OAI.UniversalTensorSquare.degreeTree62_87All`, `OAI.UniversalTensorSquare.sg31972`, `OAI.UniversalTensorSquare.sg32533`, `OAI.UniversalTensorSquare.sg32534`, `OAI.UniversalTensorSquare.sg32535`, `OAI.UniversalTensorSquare.sg32581`, `OAI.UniversalTensorSquare.sg32582`, `OAI.UniversalTensorSquare.sg32596`, `OAI.UniversalTensorSquare.sg32599`, `OAI.UniversalTensorSquare.sg32640`, `OAI.UniversalTensorSquare.sg32747`, `OAI.UniversalTensorSquare.sg32750`, `OAI.UniversalTensorSquare.sg33365`, `OAI.UniversalTensorSquare.sg33533`, `OAI.UniversalTensorSquare.sg33913`, `OAI.UniversalTensorSquare.sg33917`, `OAI.UniversalTensorSquare.sg33963`, `OAI.UniversalTensorSquare.sg34240`, `OAI.UniversalTensorSquare.sg34443`, `OAI.UniversalTensorSquare.sg34557`, `OAI.UniversalTensorSquare.sg35208`, `OAI.UniversalTensorSquare.sg36169`, `OAI.UniversalTensorSquare.sg36260`, `OAI.UniversalTensorSquare.sg37461`, `OAI.UniversalTensorSquare.sg37659`, `OAI.UniversalTensorSquare.sg37660`, `OAI.UniversalTensorSquare.sg40743`, `OAI.UniversalTensorSquare.sg41161` and `OAI.UniversalTensorSquare.sg41488` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean (declaration OAI.UniversalTensorSquare.sg4488)

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

lemma sg4488 : RowSquare [9,3,2,1,1] [3,3,3,3,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
