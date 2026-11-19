-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg616
-- name    : OAI.UniversalTensorSquare.sg616
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T22:52:10.720199+00:00
-- url     : https://prove2.me/theorems/435968b6-a2b4-4ea0-afbe-a5f1f19ca8f2
-- title:
--   OAI.UniversalTensorSquare.sg616: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg616` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg616 : RowSquare [5,2,1,1] [2,2,2,2,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree39_30All`, `OAI.UniversalTensorSquare.degreeTree41_11All`, `OAI.UniversalTensorSquare.degreeTree43_185All`, `OAI.UniversalTensorSquare.degreeTree43_228All`, `OAI.UniversalTensorSquare.degreeTree43_253All`, `OAI.UniversalTensorSquare.degreeTree43_368All`, `OAI.UniversalTensorSquare.degreeTree43_402All`, `OAI.UniversalTensorSquare.degreeTree43_421All`, `OAI.UniversalTensorSquare.degreeTree43_44All`, `OAI.UniversalTensorSquare.degreeTree43_493All`, `OAI.UniversalTensorSquare.degreeTree43_565All`, `OAI.UniversalTensorSquare.degreeTree43_56All`, `OAI.UniversalTensorSquare.degreeTree43_601All`, `OAI.UniversalTensorSquare.degreeTree43_616All`, `OAI.UniversalTensorSquare.degreeTree62_116All`, `OAI.UniversalTensorSquare.degreeTree62_549All`, `OAI.UniversalTensorSquare.degreeTree62_885All`, `OAI.UniversalTensorSquare.sg14631`, `OAI.UniversalTensorSquare.sg21782`, `OAI.UniversalTensorSquare.sg21810`, `OAI.UniversalTensorSquare.sg21835`, `OAI.UniversalTensorSquare.sg21878`, `OAI.UniversalTensorSquare.sg21884`, `OAI.UniversalTensorSquare.sg21900`, `OAI.UniversalTensorSquare.sg21901`, `OAI.UniversalTensorSquare.sg21902`, `OAI.UniversalTensorSquare.sg22146`, `OAI.UniversalTensorSquare.sg22149`, `OAI.UniversalTensorSquare.sg22255`, `OAI.UniversalTensorSquare.sg22877`, `OAI.UniversalTensorSquare.sg23121`, `OAI.UniversalTensorSquare.sg24307`, `OAI.UniversalTensorSquare.sg24427`, `OAI.UniversalTensorSquare.sg25042`, `OAI.UniversalTensorSquare.sg25180`, `OAI.UniversalTensorSquare.sg25237`, `OAI.UniversalTensorSquare.sg26023`, `OAI.UniversalTensorSquare.sg26100`, `OAI.UniversalTensorSquare.sg26115`, `OAI.UniversalTensorSquare.sg26168`, `OAI.UniversalTensorSquare.sg28808`, `OAI.UniversalTensorSquare.sg29495`, `OAI.UniversalTensorSquare.sg29902`, `OAI.UniversalTensorSquare.sg29949`, `OAI.UniversalTensorSquare.sg29951`, `OAI.UniversalTensorSquare.sg30565`, `OAI.UniversalTensorSquare.sg31461`, `OAI.UniversalTensorSquare.sg31464`, `OAI.UniversalTensorSquare.sg31470`, `OAI.UniversalTensorSquare.sg32972`, `OAI.UniversalTensorSquare.sg34562`, `OAI.UniversalTensorSquare.sg35284`, `OAI.UniversalTensorSquare.sg35372`, `OAI.UniversalTensorSquare.sg35461`, `OAI.UniversalTensorSquare.sg35467`, `OAI.UniversalTensorSquare.sg35470`, `OAI.UniversalTensorSquare.sg38064`, `OAI.UniversalTensorSquare.sg38067`, `OAI.UniversalTensorSquare.sg38068`, `OAI.UniversalTensorSquare.sg38069`, `OAI.UniversalTensorSquare.sg39059`, `OAI.UniversalTensorSquare.sg39061`, `OAI.UniversalTensorSquare.sg39063`, `OAI.UniversalTensorSquare.sg39497`, `OAI.UniversalTensorSquare.sg39498`, `OAI.UniversalTensorSquare.sg39645`, `OAI.UniversalTensorSquare.sg40657`, `OAI.UniversalTensorSquare.sg40659`, `OAI.UniversalTensorSquare.sg40660`, `OAI.UniversalTensorSquare.sg40677`, `OAI.UniversalTensorSquare.sg41360`, `OAI.UniversalTensorSquare.sg41480`, `OAI.UniversalTensorSquare.sg41773`, `OAI.UniversalTensorSquare.sg41807`, `OAI.UniversalTensorSquare.sg41823`, `OAI.UniversalTensorSquare.sg42347`, `OAI.UniversalTensorSquare.sg42621`, `OAI.UniversalTensorSquare.sg42994`, `OAI.UniversalTensorSquare.sg6800`, `OAI.UniversalTensorSquare.sg6824` and `OAI.UniversalTensorSquare.sg6834` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves3.lean (declaration OAI.UniversalTensorSquare.sg616)

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

lemma sg616 : RowSquare [5,2,1,1] [2,2,2,2,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
