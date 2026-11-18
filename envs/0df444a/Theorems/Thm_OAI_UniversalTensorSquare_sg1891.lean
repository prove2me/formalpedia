-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1891
-- name    : OAI.UniversalTensorSquare.sg1891
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:10:29.078042+00:00
-- url     : https://prove2.me/theorems/a9085d28-bb12-4bf6-8eac-249ed156c855
-- title:
--   OAI.UniversalTensorSquare.sg1891: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1891` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1891 : RowSquare [7,2,2,1] [2,2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_116All`, `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_253All`, `OAI.UniversalTensorSquare.degreeTree62_259All`, `OAI.UniversalTensorSquare.degreeTree62_273All`, `OAI.UniversalTensorSquare.degreeTree62_285All`, `OAI.UniversalTensorSquare.degreeTree62_409All`, `OAI.UniversalTensorSquare.degreeTree62_469All`, `OAI.UniversalTensorSquare.degreeTree62_519All`, `OAI.UniversalTensorSquare.degreeTree62_664All`, `OAI.UniversalTensorSquare.degreeTree62_677All`, `OAI.UniversalTensorSquare.degreeTree62_699All`, `OAI.UniversalTensorSquare.degreeTree62_709All`, `OAI.UniversalTensorSquare.degreeTree62_924All`, `OAI.UniversalTensorSquare.degreeTree62_937All`, `OAI.UniversalTensorSquare.degreeTree62_953All`, `OAI.UniversalTensorSquare.sg12509`, `OAI.UniversalTensorSquare.sg16321`, `OAI.UniversalTensorSquare.sg16333`, `OAI.UniversalTensorSquare.sg17293`, `OAI.UniversalTensorSquare.sg18435`, `OAI.UniversalTensorSquare.sg32799`, `OAI.UniversalTensorSquare.sg32802`, `OAI.UniversalTensorSquare.sg34436`, `OAI.UniversalTensorSquare.sg35467`, `OAI.UniversalTensorSquare.sg36280`, `OAI.UniversalTensorSquare.sg36556`, `OAI.UniversalTensorSquare.sg36558`, `OAI.UniversalTensorSquare.sg36560`, `OAI.UniversalTensorSquare.sg37012`, `OAI.UniversalTensorSquare.sg37487`, `OAI.UniversalTensorSquare.sg37506`, `OAI.UniversalTensorSquare.sg37738`, `OAI.UniversalTensorSquare.sg37742`, `OAI.UniversalTensorSquare.sg38369`, `OAI.UniversalTensorSquare.sg38374`, `OAI.UniversalTensorSquare.sg38757`, `OAI.UniversalTensorSquare.sg38876`, `OAI.UniversalTensorSquare.sg39325`, `OAI.UniversalTensorSquare.sg39342`, `OAI.UniversalTensorSquare.sg39522`, `OAI.UniversalTensorSquare.sg40613`, `OAI.UniversalTensorSquare.sg40751`, `OAI.UniversalTensorSquare.sg40762`, `OAI.UniversalTensorSquare.sg40763`, `OAI.UniversalTensorSquare.sg40765`, `OAI.UniversalTensorSquare.sg41413`, `OAI.UniversalTensorSquare.sg41839`, `OAI.UniversalTensorSquare.sg42420`, `OAI.UniversalTensorSquare.sg42427`, `OAI.UniversalTensorSquare.sg43009` and `OAI.UniversalTensorSquare.sg8985` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes3.lean (declaration OAI.UniversalTensorSquare.sg1891)

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

lemma sg1891 : RowSquare [7,2,2,1] [2,2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
