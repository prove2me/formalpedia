-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4949
-- name    : OAI.UniversalTensorSquare.sg4949
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:18:45.031032+00:00
-- url     : https://prove2.me/theorems/acb383c0-c671-4c9f-b89d-7f98cbef3c75
-- title:
--   OAI.UniversalTensorSquare.sg4949: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4949` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes11.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes11.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4949 : RowSquare [9,3,2,1,1,1] [3,3,3,3,3,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_0All`, `OAI.UniversalTensorSquare.degreeTree62_127All`, `OAI.UniversalTensorSquare.degreeTree62_12All`, `OAI.UniversalTensorSquare.degreeTree62_13All`, `OAI.UniversalTensorSquare.degreeTree62_146All`, `OAI.UniversalTensorSquare.degreeTree62_151All`, `OAI.UniversalTensorSquare.degreeTree62_159All`, `OAI.UniversalTensorSquare.degreeTree62_16All`, `OAI.UniversalTensorSquare.degreeTree62_20All`, `OAI.UniversalTensorSquare.degreeTree62_22All`, `OAI.UniversalTensorSquare.degreeTree62_23All`, `OAI.UniversalTensorSquare.degreeTree62_25All`, `OAI.UniversalTensorSquare.degreeTree62_2All`, `OAI.UniversalTensorSquare.degreeTree62_35All`, `OAI.UniversalTensorSquare.degreeTree62_390All`, `OAI.UniversalTensorSquare.degreeTree62_395All`, `OAI.UniversalTensorSquare.degreeTree62_39All`, `OAI.UniversalTensorSquare.degreeTree62_3All`, `OAI.UniversalTensorSquare.degreeTree62_449All`, `OAI.UniversalTensorSquare.degreeTree62_478All`, `OAI.UniversalTensorSquare.degreeTree62_577All`, `OAI.UniversalTensorSquare.degreeTree62_57All`, `OAI.UniversalTensorSquare.degreeTree62_62All`, `OAI.UniversalTensorSquare.degreeTree62_65All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.degreeTree62_75All`, `OAI.UniversalTensorSquare.degreeTree62_8All`, `OAI.UniversalTensorSquare.sg20334`, `OAI.UniversalTensorSquare.sg20341`, `OAI.UniversalTensorSquare.sg31954`, `OAI.UniversalTensorSquare.sg31969`, `OAI.UniversalTensorSquare.sg32017`, `OAI.UniversalTensorSquare.sg32021`, `OAI.UniversalTensorSquare.sg32022`, `OAI.UniversalTensorSquare.sg32023`, `OAI.UniversalTensorSquare.sg32024`, `OAI.UniversalTensorSquare.sg32025`, `OAI.UniversalTensorSquare.sg32051`, `OAI.UniversalTensorSquare.sg32052`, `OAI.UniversalTensorSquare.sg32054`, `OAI.UniversalTensorSquare.sg32139`, `OAI.UniversalTensorSquare.sg32194`, `OAI.UniversalTensorSquare.sg32210`, `OAI.UniversalTensorSquare.sg32217`, `OAI.UniversalTensorSquare.sg32326`, `OAI.UniversalTensorSquare.sg32336`, `OAI.UniversalTensorSquare.sg32438`, `OAI.UniversalTensorSquare.sg32727`, `OAI.UniversalTensorSquare.sg32728`, `OAI.UniversalTensorSquare.sg32729`, `OAI.UniversalTensorSquare.sg32731`, `OAI.UniversalTensorSquare.sg32733`, `OAI.UniversalTensorSquare.sg32734`, `OAI.UniversalTensorSquare.sg32795`, `OAI.UniversalTensorSquare.sg32796`, `OAI.UniversalTensorSquare.sg32797`, `OAI.UniversalTensorSquare.sg32805`, `OAI.UniversalTensorSquare.sg32806`, `OAI.UniversalTensorSquare.sg32807`, `OAI.UniversalTensorSquare.sg32808`, `OAI.UniversalTensorSquare.sg32849`, `OAI.UniversalTensorSquare.sg32850`, `OAI.UniversalTensorSquare.sg32851`, `OAI.UniversalTensorSquare.sg32855`, `OAI.UniversalTensorSquare.sg32856`, `OAI.UniversalTensorSquare.sg32857`, `OAI.UniversalTensorSquare.sg32860`, `OAI.UniversalTensorSquare.sg32869`, `OAI.UniversalTensorSquare.sg33086`, `OAI.UniversalTensorSquare.sg33671`, `OAI.UniversalTensorSquare.sg33678`, `OAI.UniversalTensorSquare.sg33790`, `OAI.UniversalTensorSquare.sg35111`, `OAI.UniversalTensorSquare.sg35842`, `OAI.UniversalTensorSquare.sg35847`, `OAI.UniversalTensorSquare.sg36341`, `OAI.UniversalTensorSquare.sg36342`, `OAI.UniversalTensorSquare.sg36343`, `OAI.UniversalTensorSquare.sg36346`, `OAI.UniversalTensorSquare.sg36347`, `OAI.UniversalTensorSquare.sg37053`, `OAI.UniversalTensorSquare.sg37057`, `OAI.UniversalTensorSquare.sg37062`, `OAI.UniversalTensorSquare.sg37063`, `OAI.UniversalTensorSquare.sg37064`, `OAI.UniversalTensorSquare.sg37067`, `OAI.UniversalTensorSquare.sg37507`, `OAI.UniversalTensorSquare.sg37508`, `OAI.UniversalTensorSquare.sg37509`, `OAI.UniversalTensorSquare.sg38376`, `OAI.UniversalTensorSquare.sg38377`, `OAI.UniversalTensorSquare.sg40780`, `OAI.UniversalTensorSquare.sg40781` and `OAI.UniversalTensorSquare.sg41184` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes11.lean (declaration OAI.UniversalTensorSquare.sg4949)

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

lemma sg4949 : RowSquare [9,3,2,1,1,1] [3,3,3,3,3,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
