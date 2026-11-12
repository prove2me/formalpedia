-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20515
-- name    : OAI.UniversalTensorSquare.sg20515
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:26.936382+00:00
-- url     : https://prove2.me/theorems/ce89c6ca-1310-4f2f-b3d9-734aa79cf943
-- title:
--   OAI.UniversalTensorSquare.sg20515: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20515` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20515 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,2,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_102All`, `OAI.UniversalTensorSquare.degreeTree62_110All`, `OAI.UniversalTensorSquare.degreeTree62_113All`, `OAI.UniversalTensorSquare.degreeTree62_117All`, `OAI.UniversalTensorSquare.degreeTree62_121All`, `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_12All`, `OAI.UniversalTensorSquare.degreeTree62_152All`, `OAI.UniversalTensorSquare.degreeTree62_155All`, `OAI.UniversalTensorSquare.degreeTree62_164All`, `OAI.UniversalTensorSquare.degreeTree62_182All`, `OAI.UniversalTensorSquare.degreeTree62_191All`, `OAI.UniversalTensorSquare.degreeTree62_198All`, `OAI.UniversalTensorSquare.degreeTree62_199All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_217All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_236All`, `OAI.UniversalTensorSquare.degreeTree62_23All`, `OAI.UniversalTensorSquare.degreeTree62_240All`, `OAI.UniversalTensorSquare.degreeTree62_246All`, `OAI.UniversalTensorSquare.degreeTree62_249All`, `OAI.UniversalTensorSquare.degreeTree62_256All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_259All`, `OAI.UniversalTensorSquare.degreeTree62_25All`, `OAI.UniversalTensorSquare.degreeTree62_263All`, `OAI.UniversalTensorSquare.degreeTree62_270All`, `OAI.UniversalTensorSquare.degreeTree62_274All`, `OAI.UniversalTensorSquare.degreeTree62_277All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_287All`, `OAI.UniversalTensorSquare.degreeTree62_288All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_31All`, `OAI.UniversalTensorSquare.degreeTree62_369All`, `OAI.UniversalTensorSquare.degreeTree62_435All`, `OAI.UniversalTensorSquare.degreeTree62_470All`, `OAI.UniversalTensorSquare.degreeTree62_478All`, `OAI.UniversalTensorSquare.degreeTree62_479All`, `OAI.UniversalTensorSquare.degreeTree62_486All`, `OAI.UniversalTensorSquare.degreeTree62_491All`, `OAI.UniversalTensorSquare.degreeTree62_494All`, `OAI.UniversalTensorSquare.degreeTree62_553All`, `OAI.UniversalTensorSquare.degreeTree62_602All`, `OAI.UniversalTensorSquare.degreeTree62_606All`, `OAI.UniversalTensorSquare.degreeTree62_607All`, `OAI.UniversalTensorSquare.degreeTree62_610All`, `OAI.UniversalTensorSquare.degreeTree62_665All`, `OAI.UniversalTensorSquare.degreeTree62_669All`, `OAI.UniversalTensorSquare.degreeTree62_688All`, `OAI.UniversalTensorSquare.degreeTree62_695All`, `OAI.UniversalTensorSquare.degreeTree62_705All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_709All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_714All`, `OAI.UniversalTensorSquare.degreeTree62_75All`, `OAI.UniversalTensorSquare.degreeTree62_80All`, `OAI.UniversalTensorSquare.degreeTree62_98All`, `OAI.UniversalTensorSquare.sg32319`, `OAI.UniversalTensorSquare.sg32381`, `OAI.UniversalTensorSquare.sg32390`, `OAI.UniversalTensorSquare.sg32423`, `OAI.UniversalTensorSquare.sg32430`, `OAI.UniversalTensorSquare.sg32463`, `OAI.UniversalTensorSquare.sg32731`, `OAI.UniversalTensorSquare.sg32934`, `OAI.UniversalTensorSquare.sg33122`, `OAI.UniversalTensorSquare.sg33134`, `OAI.UniversalTensorSquare.sg33183`, `OAI.UniversalTensorSquare.sg33295`, `OAI.UniversalTensorSquare.sg33307`, `OAI.UniversalTensorSquare.sg33406`, `OAI.UniversalTensorSquare.sg33690`, `OAI.UniversalTensorSquare.sg33775`, `OAI.UniversalTensorSquare.sg34058`, `OAI.UniversalTensorSquare.sg34185`, `OAI.UniversalTensorSquare.sg34194`, `OAI.UniversalTensorSquare.sg34760`, `OAI.UniversalTensorSquare.sg34847`, `OAI.UniversalTensorSquare.sg34896`, `OAI.UniversalTensorSquare.sg35012`, `OAI.UniversalTensorSquare.sg35038`, `OAI.UniversalTensorSquare.sg35045`, `OAI.UniversalTensorSquare.sg35294`, `OAI.UniversalTensorSquare.sg35330`, `OAI.UniversalTensorSquare.sg37505`, `OAI.UniversalTensorSquare.sg38190`, `OAI.UniversalTensorSquare.sg38199`, `OAI.UniversalTensorSquare.sg38474`, `OAI.UniversalTensorSquare.sg38556`, `OAI.UniversalTensorSquare.sg38593`, `OAI.UniversalTensorSquare.sg38601`, `OAI.UniversalTensorSquare.sg38731`, `OAI.UniversalTensorSquare.sg38758`, `OAI.UniversalTensorSquare.sg38762`, `OAI.UniversalTensorSquare.sg39264`, `OAI.UniversalTensorSquare.sg39372` and `OAI.UniversalTensorSquare.sg40122` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20515)

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

lemma sg20515 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,2,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
