-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4165
-- name    : OAI.UniversalTensorSquare.sg4165
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T20:24:15.7478+00:00
-- url     : https://prove2.me/theorems/29728ee1-e6c0-4140-905c-46cd6bf7f986
-- title:
--   OAI.UniversalTensorSquare.sg4165: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4165` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4165 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_95All`, `OAI.UniversalTensorSquare.sg12931`, `OAI.UniversalTensorSquare.sg18284`, `OAI.UniversalTensorSquare.sg32179`, `OAI.UniversalTensorSquare.sg32238`, `OAI.UniversalTensorSquare.sg32530`, `OAI.UniversalTensorSquare.sg33058`, `OAI.UniversalTensorSquare.sg34479`, `OAI.UniversalTensorSquare.sg35384`, `OAI.UniversalTensorSquare.sg37001`, `OAI.UniversalTensorSquare.sg38193`, `OAI.UniversalTensorSquare.sg39173`, `OAI.UniversalTensorSquare.sg40177`, `OAI.UniversalTensorSquare.sg41077`, `OAI.UniversalTensorSquare.sg42688` and `OAI.UniversalTensorSquare.sg42751` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean (declaration OAI.UniversalTensorSquare.sg4165)

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

lemma sg4165 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
