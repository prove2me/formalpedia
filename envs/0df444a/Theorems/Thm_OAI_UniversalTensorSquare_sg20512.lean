-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20512
-- name    : OAI.UniversalTensorSquare.sg20512
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:24.878105+00:00
-- url     : https://prove2.me/theorems/0ec6fa29-3b51-4f5d-9367-01a3f06d64e6
-- title:
--   OAI.UniversalTensorSquare.sg20512: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20512` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20512 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_102All`, `OAI.UniversalTensorSquare.degreeTree62_110All`, `OAI.UniversalTensorSquare.degreeTree62_113All`, `OAI.UniversalTensorSquare.degreeTree62_117All`, `OAI.UniversalTensorSquare.degreeTree62_122All`, `OAI.UniversalTensorSquare.degreeTree62_13All`, `OAI.UniversalTensorSquare.degreeTree62_152All`, `OAI.UniversalTensorSquare.degreeTree62_164All`, `OAI.UniversalTensorSquare.degreeTree62_182All`, `OAI.UniversalTensorSquare.degreeTree62_198All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_217All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_23All`, `OAI.UniversalTensorSquare.degreeTree62_249All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_259All`, `OAI.UniversalTensorSquare.degreeTree62_25All`, `OAI.UniversalTensorSquare.degreeTree62_262All`, `OAI.UniversalTensorSquare.degreeTree62_263All`, `OAI.UniversalTensorSquare.degreeTree62_274All`, `OAI.UniversalTensorSquare.degreeTree62_276All`, `OAI.UniversalTensorSquare.degreeTree62_277All`, `OAI.UniversalTensorSquare.degreeTree62_280All`, `OAI.UniversalTensorSquare.degreeTree62_287All`, `OAI.UniversalTensorSquare.degreeTree62_288All`, `OAI.UniversalTensorSquare.degreeTree62_28All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_317All`, `OAI.UniversalTensorSquare.degreeTree62_34All`, `OAI.UniversalTensorSquare.degreeTree62_491All`, `OAI.UniversalTensorSquare.degreeTree62_602All`, `OAI.UniversalTensorSquare.degreeTree62_610All`, `OAI.UniversalTensorSquare.degreeTree62_669All`, `OAI.UniversalTensorSquare.degreeTree62_707All`, `OAI.UniversalTensorSquare.degreeTree62_709All`, `OAI.UniversalTensorSquare.degreeTree62_713All`, `OAI.UniversalTensorSquare.degreeTree62_714All`, `OAI.UniversalTensorSquare.degreeTree62_75All`, `OAI.UniversalTensorSquare.degreeTree62_844All`, `OAI.UniversalTensorSquare.degreeTree62_851All`, `OAI.UniversalTensorSquare.degreeTree62_857All`, `OAI.UniversalTensorSquare.degreeTree62_882All`, `OAI.UniversalTensorSquare.degreeTree62_932All`, `OAI.UniversalTensorSquare.degreeTree62_946All`, `OAI.UniversalTensorSquare.degreeTree62_953All`, `OAI.UniversalTensorSquare.degreeTree62_98All`, `OAI.UniversalTensorSquare.sg32362`, `OAI.UniversalTensorSquare.sg32375`, `OAI.UniversalTensorSquare.sg32386`, `OAI.UniversalTensorSquare.sg32426`, `OAI.UniversalTensorSquare.sg32459`, `OAI.UniversalTensorSquare.sg32727`, `OAI.UniversalTensorSquare.sg32930`, `OAI.UniversalTensorSquare.sg33139`, `OAI.UniversalTensorSquare.sg33179`, `OAI.UniversalTensorSquare.sg33301`, `OAI.UniversalTensorSquare.sg33377`, `OAI.UniversalTensorSquare.sg33402`, `OAI.UniversalTensorSquare.sg33686`, `OAI.UniversalTensorSquare.sg33714`, `OAI.UniversalTensorSquare.sg34039`, `OAI.UniversalTensorSquare.sg34134`, `OAI.UniversalTensorSquare.sg34166`, `OAI.UniversalTensorSquare.sg34190`, `OAI.UniversalTensorSquare.sg34325`, `OAI.UniversalTensorSquare.sg34708`, `OAI.UniversalTensorSquare.sg34753`, `OAI.UniversalTensorSquare.sg34770`, `OAI.UniversalTensorSquare.sg34836`, `OAI.UniversalTensorSquare.sg34840`, `OAI.UniversalTensorSquare.sg34892`, `OAI.UniversalTensorSquare.sg34993`, `OAI.UniversalTensorSquare.sg35006`, `OAI.UniversalTensorSquare.sg35041`, `OAI.UniversalTensorSquare.sg35288`, `OAI.UniversalTensorSquare.sg35326`, `OAI.UniversalTensorSquare.sg37501`, `OAI.UniversalTensorSquare.sg38759`, `OAI.UniversalTensorSquare.sg41960`, `OAI.UniversalTensorSquare.sg42008`, `OAI.UniversalTensorSquare.sg42019`, `OAI.UniversalTensorSquare.sg42027`, `OAI.UniversalTensorSquare.sg42457`, `OAI.UniversalTensorSquare.sg42494`, `OAI.UniversalTensorSquare.sg42500`, `OAI.UniversalTensorSquare.sg42704` and `OAI.UniversalTensorSquare.sg42732` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20512)

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

lemma sg20512 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
