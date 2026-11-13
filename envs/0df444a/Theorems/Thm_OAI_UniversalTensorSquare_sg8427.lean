-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg8427
-- name    : OAI.UniversalTensorSquare.sg8427
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T22:47:07.490454+00:00
-- url     : https://prove2.me/theorems/56b8e63d-d0af-4717-8253-3e52fad4c664
-- title:
--   OAI.UniversalTensorSquare.sg8427: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg8427` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg8427 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,2,2,2,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_102All`, `OAI.UniversalTensorSquare.degreeTree43_107All`, `OAI.UniversalTensorSquare.degreeTree43_171All`, `OAI.UniversalTensorSquare.degreeTree43_192All`, `OAI.UniversalTensorSquare.degreeTree43_194All`, `OAI.UniversalTensorSquare.degreeTree43_195All`, `OAI.UniversalTensorSquare.degreeTree43_197All`, `OAI.UniversalTensorSquare.degreeTree43_198All`, `OAI.UniversalTensorSquare.degreeTree43_218All`, `OAI.UniversalTensorSquare.degreeTree43_223All`, `OAI.UniversalTensorSquare.degreeTree43_224All`, `OAI.UniversalTensorSquare.degreeTree43_236All`, `OAI.UniversalTensorSquare.degreeTree43_237All`, `OAI.UniversalTensorSquare.degreeTree43_238All`, `OAI.UniversalTensorSquare.degreeTree43_283All`, `OAI.UniversalTensorSquare.degreeTree43_293All`, `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_299All`, `OAI.UniversalTensorSquare.degreeTree43_425All`, `OAI.UniversalTensorSquare.degreeTree43_473All`, `OAI.UniversalTensorSquare.degreeTree43_483All`, `OAI.UniversalTensorSquare.degreeTree43_486All`, `OAI.UniversalTensorSquare.degreeTree43_51All`, `OAI.UniversalTensorSquare.degreeTree43_53All`, `OAI.UniversalTensorSquare.degreeTree43_56All`, `OAI.UniversalTensorSquare.degreeTree43_60All`, `OAI.UniversalTensorSquare.degreeTree43_61All`, `OAI.UniversalTensorSquare.degreeTree43_75All`, `OAI.UniversalTensorSquare.sg24719`, `OAI.UniversalTensorSquare.sg25000`, `OAI.UniversalTensorSquare.sg25048`, `OAI.UniversalTensorSquare.sg25882`, `OAI.UniversalTensorSquare.sg26194`, `OAI.UniversalTensorSquare.sg26207`, `OAI.UniversalTensorSquare.sg27539`, `OAI.UniversalTensorSquare.sg29125`, `OAI.UniversalTensorSquare.sg29684` and `OAI.UniversalTensorSquare.sg29750` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes19.lean (declaration OAI.UniversalTensorSquare.sg8427)

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

lemma sg8427 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,3,3,3,2,2,2,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
