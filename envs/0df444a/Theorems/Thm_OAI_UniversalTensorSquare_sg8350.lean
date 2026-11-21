-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8350
-- name    : OAI.UniversalTensorSquare.sg8350
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T23:38:59.325788+00:00
-- url     : https://prove2.me/theorems/4988c0e8-2aee-47c3-a4c0-f0a4a72bd326
-- title:
--   OAI.UniversalTensorSquare.sg8350: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8350` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8350 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_194All`, `OAI.UniversalTensorSquare.degreeTree43_198All`, `OAI.UniversalTensorSquare.degreeTree43_224All`, `OAI.UniversalTensorSquare.degreeTree43_243All`, `OAI.UniversalTensorSquare.degreeTree43_60All`, `OAI.UniversalTensorSquare.degreeTree43_61All`, `OAI.UniversalTensorSquare.sg24111`, `OAI.UniversalTensorSquare.sg24162`, `OAI.UniversalTensorSquare.sg24178`, `OAI.UniversalTensorSquare.sg24266`, `OAI.UniversalTensorSquare.sg24345`, `OAI.UniversalTensorSquare.sg24360`, `OAI.UniversalTensorSquare.sg24456`, `OAI.UniversalTensorSquare.sg25611`, `OAI.UniversalTensorSquare.sg25626`, `OAI.UniversalTensorSquare.sg25718`, `OAI.UniversalTensorSquare.sg25789`, `OAI.UniversalTensorSquare.sg25877`, `OAI.UniversalTensorSquare.sg26065`, `OAI.UniversalTensorSquare.sg26146`, `OAI.UniversalTensorSquare.sg26208`, `OAI.UniversalTensorSquare.sg26278`, `OAI.UniversalTensorSquare.sg26456`, `OAI.UniversalTensorSquare.sg26458`, `OAI.UniversalTensorSquare.sg26536`, `OAI.UniversalTensorSquare.sg26679`, `OAI.UniversalTensorSquare.sg26685`, `OAI.UniversalTensorSquare.sg26720` and `OAI.UniversalTensorSquare.sg27286` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean (declaration OAI.UniversalTensorSquare.sg8350)

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

lemma sg8350 : RowSquare [5,5,3,2,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
