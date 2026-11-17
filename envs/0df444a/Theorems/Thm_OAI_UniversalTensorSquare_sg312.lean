-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg312
-- name    : OAI.UniversalTensorSquare.sg312
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T23:50:24.683677+00:00
-- url     : https://prove2.me/theorems/a0c6a351-696e-4d60-b254-dcf6c5d0cd8b
-- title:
--   OAI.UniversalTensorSquare.sg312: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg312` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg312 : RowSquare [4,1,1,1,1] [2,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree41_11All`, `OAI.UniversalTensorSquare.degreeTree43_5All`, `OAI.UniversalTensorSquare.degreeTree62_372All`, `OAI.UniversalTensorSquare.sg10100`, `OAI.UniversalTensorSquare.sg23969`, `OAI.UniversalTensorSquare.sg23972`, `OAI.UniversalTensorSquare.sg24066`, `OAI.UniversalTensorSquare.sg24069`, `OAI.UniversalTensorSquare.sg24138`, `OAI.UniversalTensorSquare.sg24139`, `OAI.UniversalTensorSquare.sg24140`, `OAI.UniversalTensorSquare.sg24188`, `OAI.UniversalTensorSquare.sg24217`, `OAI.UniversalTensorSquare.sg24292`, `OAI.UniversalTensorSquare.sg24313`, `OAI.UniversalTensorSquare.sg24349`, `OAI.UniversalTensorSquare.sg24425`, `OAI.UniversalTensorSquare.sg25422`, `OAI.UniversalTensorSquare.sg25507`, `OAI.UniversalTensorSquare.sg25522`, `OAI.UniversalTensorSquare.sg25559`, `OAI.UniversalTensorSquare.sg25560`, `OAI.UniversalTensorSquare.sg25589`, `OAI.UniversalTensorSquare.sg25604`, `OAI.UniversalTensorSquare.sg25615`, `OAI.UniversalTensorSquare.sg25626`, `OAI.UniversalTensorSquare.sg25653`, `OAI.UniversalTensorSquare.sg25716`, `OAI.UniversalTensorSquare.sg25859`, `OAI.UniversalTensorSquare.sg25874`, `OAI.UniversalTensorSquare.sg25875`, `OAI.UniversalTensorSquare.sg26807`, `OAI.UniversalTensorSquare.sg28128`, `OAI.UniversalTensorSquare.sg28134`, `OAI.UniversalTensorSquare.sg28276`, `OAI.UniversalTensorSquare.sg28279`, `OAI.UniversalTensorSquare.sg28381`, `OAI.UniversalTensorSquare.sg28384`, `OAI.UniversalTensorSquare.sg28824`, `OAI.UniversalTensorSquare.sg29121`, `OAI.UniversalTensorSquare.sg29134`, `OAI.UniversalTensorSquare.sg29507`, `OAI.UniversalTensorSquare.sg29737` and `OAI.UniversalTensorSquare.sg5533` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes0.lean (declaration OAI.UniversalTensorSquare.sg312)

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

lemma sg312 : RowSquare [4,1,1,1,1] [2,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
