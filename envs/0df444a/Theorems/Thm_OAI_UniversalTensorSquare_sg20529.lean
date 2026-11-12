-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20529
-- name    : OAI.UniversalTensorSquare.sg20529
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:52:07.295644+00:00
-- url     : https://prove2.me/theorems/5a106f68-ce95-40bf-8371-b3506aa8fb1b
-- title:
--   OAI.UniversalTensorSquare.sg20529: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20529` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20529 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,3,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_328All`, `OAI.UniversalTensorSquare.degreeTree62_329All`, `OAI.UniversalTensorSquare.degreeTree62_360All`, `OAI.UniversalTensorSquare.degreeTree62_364All`, `OAI.UniversalTensorSquare.degreeTree62_372All`, `OAI.UniversalTensorSquare.degreeTree62_374All`, `OAI.UniversalTensorSquare.degreeTree62_384All`, `OAI.UniversalTensorSquare.degreeTree62_385All`, `OAI.UniversalTensorSquare.degreeTree62_389All`, `OAI.UniversalTensorSquare.degreeTree62_390All`, `OAI.UniversalTensorSquare.degreeTree62_465All`, `OAI.UniversalTensorSquare.degreeTree62_469All`, `OAI.UniversalTensorSquare.degreeTree62_470All`, `OAI.UniversalTensorSquare.degreeTree62_478All`, `OAI.UniversalTensorSquare.degreeTree62_485All`, `OAI.UniversalTensorSquare.degreeTree62_486All`, `OAI.UniversalTensorSquare.degreeTree62_491All`, `OAI.UniversalTensorSquare.degreeTree62_494All`, `OAI.UniversalTensorSquare.degreeTree62_499All`, `OAI.UniversalTensorSquare.degreeTree62_502All`, `OAI.UniversalTensorSquare.degreeTree62_512All`, `OAI.UniversalTensorSquare.degreeTree62_525All`, `OAI.UniversalTensorSquare.degreeTree62_67All`, `OAI.UniversalTensorSquare.degreeTree62_749All`, `OAI.UniversalTensorSquare.degreeTree62_755All`, `OAI.UniversalTensorSquare.degreeTree62_760All`, `OAI.UniversalTensorSquare.degreeTree62_781All`, `OAI.UniversalTensorSquare.degreeTree62_795All`, `OAI.UniversalTensorSquare.sg32787`, `OAI.UniversalTensorSquare.sg32833`, `OAI.UniversalTensorSquare.sg35482`, `OAI.UniversalTensorSquare.sg35590`, `OAI.UniversalTensorSquare.sg35636`, `OAI.UniversalTensorSquare.sg35959`, `OAI.UniversalTensorSquare.sg36020`, `OAI.UniversalTensorSquare.sg36078`, `OAI.UniversalTensorSquare.sg36084`, `OAI.UniversalTensorSquare.sg36104`, `OAI.UniversalTensorSquare.sg36109`, `OAI.UniversalTensorSquare.sg36188`, `OAI.UniversalTensorSquare.sg36227`, `OAI.UniversalTensorSquare.sg36247`, `OAI.UniversalTensorSquare.sg36315`, `OAI.UniversalTensorSquare.sg36347`, `OAI.UniversalTensorSquare.sg37137`, `OAI.UniversalTensorSquare.sg37161`, `OAI.UniversalTensorSquare.sg37192`, `OAI.UniversalTensorSquare.sg37241`, `OAI.UniversalTensorSquare.sg37285`, `OAI.UniversalTensorSquare.sg37289`, `OAI.UniversalTensorSquare.sg37352`, `OAI.UniversalTensorSquare.sg37434`, `OAI.UniversalTensorSquare.sg37562`, `OAI.UniversalTensorSquare.sg37591`, `OAI.UniversalTensorSquare.sg37604`, `OAI.UniversalTensorSquare.sg37678`, `OAI.UniversalTensorSquare.sg37702`, `OAI.UniversalTensorSquare.sg40326`, `OAI.UniversalTensorSquare.sg40351`, `OAI.UniversalTensorSquare.sg40368`, `OAI.UniversalTensorSquare.sg40562`, `OAI.UniversalTensorSquare.sg40565`, `OAI.UniversalTensorSquare.sg40596`, `OAI.UniversalTensorSquare.sg40607`, `OAI.UniversalTensorSquare.sg40628`, `OAI.UniversalTensorSquare.sg40640`, `OAI.UniversalTensorSquare.sg40643`, `OAI.UniversalTensorSquare.sg40672` and `OAI.UniversalTensorSquare.sg40702` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20529)

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

lemma sg20529 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,3,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
