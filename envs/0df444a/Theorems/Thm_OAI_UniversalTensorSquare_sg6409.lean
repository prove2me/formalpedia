-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg6409
-- name    : OAI.UniversalTensorSquare.sg6409
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:55:18.815961+00:00
-- url     : https://prove2.me/theorems/71fd26b4-4842-4563-bef9-ae69ce011822
-- title:
--   OAI.UniversalTensorSquare.sg6409: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg6409` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg6409 : RowSquare [6,5,2,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_3All`, `OAI.UniversalTensorSquare.sg21860`, `OAI.UniversalTensorSquare.sg21875`, `OAI.UniversalTensorSquare.sg21883`, `OAI.UniversalTensorSquare.sg21887`, `OAI.UniversalTensorSquare.sg21895`, `OAI.UniversalTensorSquare.sg21900`, `OAI.UniversalTensorSquare.sg21902`, `OAI.UniversalTensorSquare.sg21921`, `OAI.UniversalTensorSquare.sg21925`, `OAI.UniversalTensorSquare.sg21943`, `OAI.UniversalTensorSquare.sg21977`, `OAI.UniversalTensorSquare.sg21978`, `OAI.UniversalTensorSquare.sg21982`, `OAI.UniversalTensorSquare.sg21993`, `OAI.UniversalTensorSquare.sg22015`, `OAI.UniversalTensorSquare.sg22027`, `OAI.UniversalTensorSquare.sg22029`, `OAI.UniversalTensorSquare.sg22035`, `OAI.UniversalTensorSquare.sg22037`, `OAI.UniversalTensorSquare.sg22065`, `OAI.UniversalTensorSquare.sg22072`, `OAI.UniversalTensorSquare.sg22074`, `OAI.UniversalTensorSquare.sg22079`, `OAI.UniversalTensorSquare.sg22082` and `OAI.UniversalTensorSquare.sg22356` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes14.lean (declaration OAI.UniversalTensorSquare.sg6409)

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

lemma sg6409 : RowSquare [6,5,2,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
