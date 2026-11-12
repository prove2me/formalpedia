-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg20516
-- name    : OAI.UniversalTensorSquare.sg20516
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T21:51:30.168525+00:00
-- url     : https://prove2.me/theorems/8fbaf7c8-5da2-4f86-9ae4-8744390c5f0b
-- title:
--   OAI.UniversalTensorSquare.sg20516: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg20516` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg20516 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,3,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_102All`, `OAI.UniversalTensorSquare.degreeTree62_110All`, `OAI.UniversalTensorSquare.degreeTree62_113All`, `OAI.UniversalTensorSquare.degreeTree62_117All`, `OAI.UniversalTensorSquare.degreeTree62_121All`, `OAI.UniversalTensorSquare.degreeTree62_12All`, `OAI.UniversalTensorSquare.degreeTree62_152All`, `OAI.UniversalTensorSquare.degreeTree62_155All`, `OAI.UniversalTensorSquare.degreeTree62_159All`, `OAI.UniversalTensorSquare.degreeTree62_182All`, `OAI.UniversalTensorSquare.degreeTree62_183All`, `OAI.UniversalTensorSquare.degreeTree62_191All`, `OAI.UniversalTensorSquare.degreeTree62_193All`, `OAI.UniversalTensorSquare.degreeTree62_198All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_217All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_236All`, `OAI.UniversalTensorSquare.degreeTree62_23All`, `OAI.UniversalTensorSquare.degreeTree62_240All`, `OAI.UniversalTensorSquare.degreeTree62_246All`, `OAI.UniversalTensorSquare.degreeTree62_249All`, `OAI.UniversalTensorSquare.degreeTree62_256All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_259All`, `OAI.UniversalTensorSquare.degreeTree62_25All`, `OAI.UniversalTensorSquare.degreeTree62_263All`, `OAI.UniversalTensorSquare.degreeTree62_270All`, `OAI.UniversalTensorSquare.degreeTree62_274All`, `OAI.UniversalTensorSquare.degreeTree62_279All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_287All`, `OAI.UniversalTensorSquare.degreeTree62_288All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_31All`, `OAI.UniversalTensorSquare.degreeTree62_356All`, `OAI.UniversalTensorSquare.degreeTree62_366All`, `OAI.UniversalTensorSquare.degreeTree62_367All`, `OAI.UniversalTensorSquare.degreeTree62_369All`, `OAI.UniversalTensorSquare.degreeTree62_78All`, `OAI.UniversalTensorSquare.degreeTree62_80All`, `OAI.UniversalTensorSquare.degreeTree62_84All`, `OAI.UniversalTensorSquare.degreeTree62_98All`, `OAI.UniversalTensorSquare.degreeTree62_99All`, `OAI.UniversalTensorSquare.sg32321`, `OAI.UniversalTensorSquare.sg32383`, `OAI.UniversalTensorSquare.sg32392`, `OAI.UniversalTensorSquare.sg32425`, `OAI.UniversalTensorSquare.sg32432`, `OAI.UniversalTensorSquare.sg32465`, `OAI.UniversalTensorSquare.sg32733`, `OAI.UniversalTensorSquare.sg32936`, `OAI.UniversalTensorSquare.sg33145`, `OAI.UniversalTensorSquare.sg33185`, `OAI.UniversalTensorSquare.sg33297`, `OAI.UniversalTensorSquare.sg33309`, `OAI.UniversalTensorSquare.sg33345`, `OAI.UniversalTensorSquare.sg33408`, `OAI.UniversalTensorSquare.sg33692`, `OAI.UniversalTensorSquare.sg33777`, `OAI.UniversalTensorSquare.sg34060`, `OAI.UniversalTensorSquare.sg34143`, `OAI.UniversalTensorSquare.sg34187`, `OAI.UniversalTensorSquare.sg34196`, `OAI.UniversalTensorSquare.sg34223`, `OAI.UniversalTensorSquare.sg34762`, `OAI.UniversalTensorSquare.sg34898`, `OAI.UniversalTensorSquare.sg35014`, `OAI.UniversalTensorSquare.sg35040`, `OAI.UniversalTensorSquare.sg35047`, `OAI.UniversalTensorSquare.sg35332` and `OAI.UniversalTensorSquare.sg36029` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes49.lean (declaration OAI.UniversalTensorSquare.sg20516)

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

lemma sg20516 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,3,3,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
