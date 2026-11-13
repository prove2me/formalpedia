-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg798
-- name    : OAI.UniversalTensorSquare.sg798
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:44:13.275446+00:00
-- url     : https://prove2.me/theorems/70687e17-41f4-4eed-8606-2751250922d5
-- title:
--   OAI.UniversalTensorSquare.sg798: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg798` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg798 : RowSquare [3,3,3,1] [2,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_311All`, `OAI.UniversalTensorSquare.degreeTree62_313All`, `OAI.UniversalTensorSquare.degreeTree62_318All`, `OAI.UniversalTensorSquare.degreeTree62_339All`, `OAI.UniversalTensorSquare.degreeTree62_381All`, `OAI.UniversalTensorSquare.degreeTree62_394All`, `OAI.UniversalTensorSquare.degreeTree62_743All`, `OAI.UniversalTensorSquare.degreeTree62_749All`, `OAI.UniversalTensorSquare.degreeTree62_755All`, `OAI.UniversalTensorSquare.degreeTree62_758All`, `OAI.UniversalTensorSquare.degreeTree62_975All`, `OAI.UniversalTensorSquare.degreeTree62_978All`, `OAI.UniversalTensorSquare.degreeTree62_981All`, `OAI.UniversalTensorSquare.degreeTree62_998All`, `OAI.UniversalTensorSquare.degreeTree62_999All`, `OAI.UniversalTensorSquare.sg35490`, `OAI.UniversalTensorSquare.sg35516`, `OAI.UniversalTensorSquare.sg35518`, `OAI.UniversalTensorSquare.sg35520`, `OAI.UniversalTensorSquare.sg35675`, `OAI.UniversalTensorSquare.sg35679`, `OAI.UniversalTensorSquare.sg35681`, `OAI.UniversalTensorSquare.sg35683`, `OAI.UniversalTensorSquare.sg35720`, `OAI.UniversalTensorSquare.sg35724`, `OAI.UniversalTensorSquare.sg35726`, `OAI.UniversalTensorSquare.sg35733`, `OAI.UniversalTensorSquare.sg35735`, `OAI.UniversalTensorSquare.sg35737`, `OAI.UniversalTensorSquare.sg36362`, `OAI.UniversalTensorSquare.sg36363`, `OAI.UniversalTensorSquare.sg40235`, `OAI.UniversalTensorSquare.sg40237`, `OAI.UniversalTensorSquare.sg40238`, `OAI.UniversalTensorSquare.sg40249`, `OAI.UniversalTensorSquare.sg40251`, `OAI.UniversalTensorSquare.sg40252`, `OAI.UniversalTensorSquare.sg40274`, `OAI.UniversalTensorSquare.sg40277`, `OAI.UniversalTensorSquare.sg40278`, `OAI.UniversalTensorSquare.sg40282`, `OAI.UniversalTensorSquare.sg40284`, `OAI.UniversalTensorSquare.sg40285`, `OAI.UniversalTensorSquare.sg40373` and `OAI.UniversalTensorSquare.sg42948` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean (declaration OAI.UniversalTensorSquare.sg798)

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

lemma sg798 : RowSquare [3,3,3,1] [2,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
