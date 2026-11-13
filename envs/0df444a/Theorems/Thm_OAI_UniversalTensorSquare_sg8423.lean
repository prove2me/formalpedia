-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8423
-- name    : OAI.UniversalTensorSquare.sg8423
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:47:07.971414+00:00
-- url     : https://prove2.me/theorems/a9b57e1b-b332-4a17-92b1-100a648e0623
-- title:
--   OAI.UniversalTensorSquare.sg8423: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8423` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8423 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_143All`, `OAI.UniversalTensorSquare.degreeTree43_159All`, `OAI.UniversalTensorSquare.degreeTree43_165All`, `OAI.UniversalTensorSquare.degreeTree43_167All`, `OAI.UniversalTensorSquare.degreeTree43_171All`, `OAI.UniversalTensorSquare.degreeTree43_175All`, `OAI.UniversalTensorSquare.degreeTree43_176All`, `OAI.UniversalTensorSquare.degreeTree43_199All`, `OAI.UniversalTensorSquare.degreeTree43_205All`, `OAI.UniversalTensorSquare.degreeTree43_206All`, `OAI.UniversalTensorSquare.degreeTree43_213All`, `OAI.UniversalTensorSquare.degreeTree43_216All`, `OAI.UniversalTensorSquare.degreeTree43_218All`, `OAI.UniversalTensorSquare.degreeTree43_220All`, `OAI.UniversalTensorSquare.degreeTree43_223All`, `OAI.UniversalTensorSquare.degreeTree43_242All`, `OAI.UniversalTensorSquare.degreeTree43_268All`, `OAI.UniversalTensorSquare.degreeTree43_269All`, `OAI.UniversalTensorSquare.degreeTree43_275All`, `OAI.UniversalTensorSquare.degreeTree43_277All`, `OAI.UniversalTensorSquare.degreeTree43_278All`, `OAI.UniversalTensorSquare.degreeTree43_27All`, `OAI.UniversalTensorSquare.degreeTree43_283All`, `OAI.UniversalTensorSquare.degreeTree43_289All`, `OAI.UniversalTensorSquare.degreeTree43_28All`, `OAI.UniversalTensorSquare.degreeTree43_290All`, `OAI.UniversalTensorSquare.degreeTree43_292All`, `OAI.UniversalTensorSquare.degreeTree43_293All`, `OAI.UniversalTensorSquare.degreeTree43_31All`, `OAI.UniversalTensorSquare.degreeTree43_33All`, `OAI.UniversalTensorSquare.degreeTree43_351All`, `OAI.UniversalTensorSquare.degreeTree43_35All`, `OAI.UniversalTensorSquare.degreeTree43_37All`, `OAI.UniversalTensorSquare.degreeTree43_389All`, `OAI.UniversalTensorSquare.degreeTree43_397All`, `OAI.UniversalTensorSquare.degreeTree43_400All`, `OAI.UniversalTensorSquare.degreeTree43_406All`, `OAI.UniversalTensorSquare.degreeTree43_43All`, `OAI.UniversalTensorSquare.degreeTree43_456All`, `OAI.UniversalTensorSquare.degreeTree43_457All`, `OAI.UniversalTensorSquare.degreeTree43_466All`, `OAI.UniversalTensorSquare.degreeTree43_467All`, `OAI.UniversalTensorSquare.degreeTree43_470All`, `OAI.UniversalTensorSquare.degreeTree43_503All`, `OAI.UniversalTensorSquare.degreeTree43_512All`, `OAI.UniversalTensorSquare.degreeTree43_513All`, `OAI.UniversalTensorSquare.degreeTree43_518All`, `OAI.UniversalTensorSquare.degreeTree43_522All`, `OAI.UniversalTensorSquare.degreeTree43_527All`, `OAI.UniversalTensorSquare.degreeTree43_528All`, `OAI.UniversalTensorSquare.degreeTree43_530All`, `OAI.UniversalTensorSquare.degreeTree43_539All`, `OAI.UniversalTensorSquare.degreeTree43_544All`, `OAI.UniversalTensorSquare.degreeTree43_558All`, `OAI.UniversalTensorSquare.degreeTree43_560All`, `OAI.UniversalTensorSquare.degreeTree43_561All`, `OAI.UniversalTensorSquare.degreeTree43_568All`, `OAI.UniversalTensorSquare.degreeTree43_570All`, `OAI.UniversalTensorSquare.degreeTree43_572All`, `OAI.UniversalTensorSquare.degreeTree43_573All`, `OAI.UniversalTensorSquare.degreeTree43_576All`, `OAI.UniversalTensorSquare.degreeTree43_580All`, `OAI.UniversalTensorSquare.degreeTree43_63All`, `OAI.UniversalTensorSquare.degreeTree43_67All`, `OAI.UniversalTensorSquare.degreeTree43_69All`, `OAI.UniversalTensorSquare.degreeTree43_70All`, `OAI.UniversalTensorSquare.degreeTree43_72All`, `OAI.UniversalTensorSquare.degreeTree43_75All`, `OAI.UniversalTensorSquare.sg23780`, `OAI.UniversalTensorSquare.sg23794`, `OAI.UniversalTensorSquare.sg23808`, `OAI.UniversalTensorSquare.sg23820`, `OAI.UniversalTensorSquare.sg24558`, `OAI.UniversalTensorSquare.sg24710`, `OAI.UniversalTensorSquare.sg25381`, `OAI.UniversalTensorSquare.sg25457`, `OAI.UniversalTensorSquare.sg25472`, `OAI.UniversalTensorSquare.sg25474`, `OAI.UniversalTensorSquare.sg25487`, `OAI.UniversalTensorSquare.sg25491`, `OAI.UniversalTensorSquare.sg25504`, `OAI.UniversalTensorSquare.sg25674`, `OAI.UniversalTensorSquare.sg25691`, `OAI.UniversalTensorSquare.sg25695`, `OAI.UniversalTensorSquare.sg25707`, `OAI.UniversalTensorSquare.sg25712`, `OAI.UniversalTensorSquare.sg25715`, `OAI.UniversalTensorSquare.sg25724`, `OAI.UniversalTensorSquare.sg25729`, `OAI.UniversalTensorSquare.sg25764`, `OAI.UniversalTensorSquare.sg25857`, `OAI.UniversalTensorSquare.sg27485`, `OAI.UniversalTensorSquare.sg28754`, `OAI.UniversalTensorSquare.sg28850`, `OAI.UniversalTensorSquare.sg29325`, `OAI.UniversalTensorSquare.sg29331`, `OAI.UniversalTensorSquare.sg29433`, `OAI.UniversalTensorSquare.sg29444`, `OAI.UniversalTensorSquare.sg29447`, `OAI.UniversalTensorSquare.sg29478`, `OAI.UniversalTensorSquare.sg29496`, `OAI.UniversalTensorSquare.sg29521`, `OAI.UniversalTensorSquare.sg29633`, `OAI.UniversalTensorSquare.sg29681`, `OAI.UniversalTensorSquare.sg29694`, `OAI.UniversalTensorSquare.sg29735`, `OAI.UniversalTensorSquare.sg29746` and `OAI.UniversalTensorSquare.sg30378` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean (declaration OAI.UniversalTensorSquare.sg8423)

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

lemma sg8423 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
