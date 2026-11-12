-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1039
-- name    : OAI.UniversalTensorSquare.sg1039
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:29:20.939925+00:00
-- url     : https://prove2.me/theorems/55001c53-2381-4f29-8373-114d569f47a8
-- title:
--   OAI.UniversalTensorSquare.sg1039: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1039` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1039 : RowSquare [6,2,1,1] [3,3,2,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_242All`, `OAI.UniversalTensorSquare.degreeTree43_395All`, `OAI.UniversalTensorSquare.degreeTree43_536All`, `OAI.UniversalTensorSquare.degreeTree43_627All`, `OAI.UniversalTensorSquare.degreeTree43_97All`, `OAI.UniversalTensorSquare.sg21913`, `OAI.UniversalTensorSquare.sg23448`, `OAI.UniversalTensorSquare.sg24585`, `OAI.UniversalTensorSquare.sg24623`, `OAI.UniversalTensorSquare.sg24806`, `OAI.UniversalTensorSquare.sg25007`, `OAI.UniversalTensorSquare.sg27194`, `OAI.UniversalTensorSquare.sg27337`, `OAI.UniversalTensorSquare.sg27535`, `OAI.UniversalTensorSquare.sg29430`, `OAI.UniversalTensorSquare.sg29432`, `OAI.UniversalTensorSquare.sg30218`, `OAI.UniversalTensorSquare.sg30560`, `OAI.UniversalTensorSquare.sg31006`, `OAI.UniversalTensorSquare.sg31031`, `OAI.UniversalTensorSquare.sg31044`, `OAI.UniversalTensorSquare.sg31267`, `OAI.UniversalTensorSquare.sg31291`, `OAI.UniversalTensorSquare.sg31303`, `OAI.UniversalTensorSquare.sg31504`, `OAI.UniversalTensorSquare.sg31510`, `OAI.UniversalTensorSquare.sg31727`, `OAI.UniversalTensorSquare.sg7213`, `OAI.UniversalTensorSquare.sg7218`, `OAI.UniversalTensorSquare.sg9964` and `OAI.UniversalTensorSquare.sg9970` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean (declaration OAI.UniversalTensorSquare.sg1039)

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

lemma sg1039 : RowSquare [6,2,1,1] [3,3,2,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
