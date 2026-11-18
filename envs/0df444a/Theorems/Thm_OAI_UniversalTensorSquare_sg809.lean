-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg809
-- name    : OAI.UniversalTensorSquare.sg809
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T23:35:43.593204+00:00
-- url     : https://prove2.me/theorems/9556b788-ebb8-4625-8dfd-816fa302eeb1
-- title:
--   OAI.UniversalTensorSquare.sg809: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg809` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg809 : RowSquare [4,2,1,1,1,1] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_102All`, `OAI.UniversalTensorSquare.degreeTree43_198All`, `OAI.UniversalTensorSquare.degreeTree43_242All`, `OAI.UniversalTensorSquare.degreeTree43_244All`, `OAI.UniversalTensorSquare.degreeTree43_256All`, `OAI.UniversalTensorSquare.degreeTree43_283All`, `OAI.UniversalTensorSquare.degreeTree43_292All`, `OAI.UniversalTensorSquare.degreeTree43_299All`, `OAI.UniversalTensorSquare.degreeTree43_33All`, `OAI.UniversalTensorSquare.degreeTree43_35All`, `OAI.UniversalTensorSquare.degreeTree43_480All`, `OAI.UniversalTensorSquare.degreeTree43_493All`, `OAI.UniversalTensorSquare.degreeTree43_544All`, `OAI.UniversalTensorSquare.degreeTree43_599All`, `OAI.UniversalTensorSquare.degreeTree43_645All`, `OAI.UniversalTensorSquare.degreeTree43_70All`, `OAI.UniversalTensorSquare.degreeTree43_83All`, `OAI.UniversalTensorSquare.degreeTree43_95All`, `OAI.UniversalTensorSquare.degreeTree43_97All`, `OAI.UniversalTensorSquare.degreeTree62_57All`, `OAI.UniversalTensorSquare.degreeTree62_67All`, `OAI.UniversalTensorSquare.degreeTree62_72All`, `OAI.UniversalTensorSquare.degreeTree62_736All`, `OAI.UniversalTensorSquare.degreeTree62_77All`, `OAI.UniversalTensorSquare.degreeTree62_872All`, `OAI.UniversalTensorSquare.sg11850`, `OAI.UniversalTensorSquare.sg11858`, `OAI.UniversalTensorSquare.sg11864`, `OAI.UniversalTensorSquare.sg11954`, `OAI.UniversalTensorSquare.sg21929`, `OAI.UniversalTensorSquare.sg24189`, `OAI.UniversalTensorSquare.sg24192`, `OAI.UniversalTensorSquare.sg24379`, `OAI.UniversalTensorSquare.sg24469`, `OAI.UniversalTensorSquare.sg24471`, `OAI.UniversalTensorSquare.sg24481`, `OAI.UniversalTensorSquare.sg24550`, `OAI.UniversalTensorSquare.sg24705`, `OAI.UniversalTensorSquare.sg25260`, `OAI.UniversalTensorSquare.sg25361`, `OAI.UniversalTensorSquare.sg27305`, `OAI.UniversalTensorSquare.sg30688`, `OAI.UniversalTensorSquare.sg30827`, `OAI.UniversalTensorSquare.sg30829`, `OAI.UniversalTensorSquare.sg30968`, `OAI.UniversalTensorSquare.sg30970`, `OAI.UniversalTensorSquare.sg31229`, `OAI.UniversalTensorSquare.sg31298`, `OAI.UniversalTensorSquare.sg31325`, `OAI.UniversalTensorSquare.sg31333`, `OAI.UniversalTensorSquare.sg31334`, `OAI.UniversalTensorSquare.sg31340`, `OAI.UniversalTensorSquare.sg31408`, `OAI.UniversalTensorSquare.sg31422`, `OAI.UniversalTensorSquare.sg32194`, `OAI.UniversalTensorSquare.sg32679`, `OAI.UniversalTensorSquare.sg32910`, `OAI.UniversalTensorSquare.sg33060`, `OAI.UniversalTensorSquare.sg33121`, `OAI.UniversalTensorSquare.sg35469`, `OAI.UniversalTensorSquare.sg36044`, `OAI.UniversalTensorSquare.sg36046`, `OAI.UniversalTensorSquare.sg36204`, `OAI.UniversalTensorSquare.sg36206`, `OAI.UniversalTensorSquare.sg36315`, `OAI.UniversalTensorSquare.sg36316`, `OAI.UniversalTensorSquare.sg36319`, `OAI.UniversalTensorSquare.sg36321`, `OAI.UniversalTensorSquare.sg36542`, `OAI.UniversalTensorSquare.sg36544`, `OAI.UniversalTensorSquare.sg36552`, `OAI.UniversalTensorSquare.sg36554`, `OAI.UniversalTensorSquare.sg37285`, `OAI.UniversalTensorSquare.sg37288`, `OAI.UniversalTensorSquare.sg37289`, `OAI.UniversalTensorSquare.sg38567`, `OAI.UniversalTensorSquare.sg38568`, `OAI.UniversalTensorSquare.sg38570`, `OAI.UniversalTensorSquare.sg38571`, `OAI.UniversalTensorSquare.sg38573`, `OAI.UniversalTensorSquare.sg39087`, `OAI.UniversalTensorSquare.sg42017`, `OAI.UniversalTensorSquare.sg42679`, `OAI.UniversalTensorSquare.sg42680`, `OAI.UniversalTensorSquare.sg4304` and `OAI.UniversalTensorSquare.sg6410` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg809)

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

lemma sg809 : RowSquare [4,2,1,1,1,1] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
