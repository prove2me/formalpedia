-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8425
-- name    : OAI.UniversalTensorSquare.sg8425
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:47:10.248244+00:00
-- url     : https://prove2.me/theorems/92ddcbe0-99a0-43f6-9780-6824b9ae4c24
-- title:
--   OAI.UniversalTensorSquare.sg8425: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8425` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8425 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_103All`, `OAI.UniversalTensorSquare.degreeTree43_146All`, `OAI.UniversalTensorSquare.degreeTree43_165All`, `OAI.UniversalTensorSquare.degreeTree43_167All`, `OAI.UniversalTensorSquare.degreeTree43_184All`, `OAI.UniversalTensorSquare.degreeTree43_187All`, `OAI.UniversalTensorSquare.degreeTree43_190All`, `OAI.UniversalTensorSquare.degreeTree43_191All`, `OAI.UniversalTensorSquare.degreeTree43_194All`, `OAI.UniversalTensorSquare.degreeTree43_195All`, `OAI.UniversalTensorSquare.degreeTree43_199All`, `OAI.UniversalTensorSquare.degreeTree43_213All`, `OAI.UniversalTensorSquare.degreeTree43_215All`, `OAI.UniversalTensorSquare.degreeTree43_216All`, `OAI.UniversalTensorSquare.degreeTree43_218All`, `OAI.UniversalTensorSquare.degreeTree43_230All`, `OAI.UniversalTensorSquare.degreeTree43_233All`, `OAI.UniversalTensorSquare.degreeTree43_236All`, `OAI.UniversalTensorSquare.degreeTree43_237All`, `OAI.UniversalTensorSquare.degreeTree43_277All`, `OAI.UniversalTensorSquare.degreeTree43_289All`, `OAI.UniversalTensorSquare.degreeTree43_293All`, `OAI.UniversalTensorSquare.degreeTree43_295All`, `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_299All`, `OAI.UniversalTensorSquare.degreeTree43_31All`, `OAI.UniversalTensorSquare.degreeTree43_33All`, `OAI.UniversalTensorSquare.degreeTree43_397All`, `OAI.UniversalTensorSquare.degreeTree43_420All`, `OAI.UniversalTensorSquare.degreeTree43_44All`, `OAI.UniversalTensorSquare.degreeTree43_46All`, `OAI.UniversalTensorSquare.degreeTree43_471All`, `OAI.UniversalTensorSquare.degreeTree43_479All`, `OAI.UniversalTensorSquare.degreeTree43_480All`, `OAI.UniversalTensorSquare.degreeTree43_483All`, `OAI.UniversalTensorSquare.degreeTree43_486All`, `OAI.UniversalTensorSquare.degreeTree43_488All`, `OAI.UniversalTensorSquare.degreeTree43_489All`, `OAI.UniversalTensorSquare.degreeTree43_513All`, `OAI.UniversalTensorSquare.degreeTree43_51All`, `OAI.UniversalTensorSquare.degreeTree43_522All`, `OAI.UniversalTensorSquare.degreeTree43_527All`, `OAI.UniversalTensorSquare.degreeTree43_528All`, `OAI.UniversalTensorSquare.degreeTree43_530All`, `OAI.UniversalTensorSquare.degreeTree43_536All`, `OAI.UniversalTensorSquare.degreeTree43_53All`, `OAI.UniversalTensorSquare.degreeTree43_70All`, `OAI.UniversalTensorSquare.degreeTree43_72All`, `OAI.UniversalTensorSquare.degreeTree43_97All`, `OAI.UniversalTensorSquare.sg24633`, `OAI.UniversalTensorSquare.sg24851`, `OAI.UniversalTensorSquare.sg24899`, `OAI.UniversalTensorSquare.sg24928`, `OAI.UniversalTensorSquare.sg24975`, `OAI.UniversalTensorSquare.sg25542`, `OAI.UniversalTensorSquare.sg25561`, `OAI.UniversalTensorSquare.sg25697`, `OAI.UniversalTensorSquare.sg25800`, `OAI.UniversalTensorSquare.sg27530`, `OAI.UniversalTensorSquare.sg28976`, `OAI.UniversalTensorSquare.sg29056`, `OAI.UniversalTensorSquare.sg29448`, `OAI.UniversalTensorSquare.sg29634`, `OAI.UniversalTensorSquare.sg29636`, `OAI.UniversalTensorSquare.sg29696`, `OAI.UniversalTensorSquare.sg29844` and `OAI.UniversalTensorSquare.sg29883` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean (declaration OAI.UniversalTensorSquare.sg8425)

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

lemma sg8425 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
