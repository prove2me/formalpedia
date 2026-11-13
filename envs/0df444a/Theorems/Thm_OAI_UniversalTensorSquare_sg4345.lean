-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4345
-- name    : OAI.UniversalTensorSquare.sg4345
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T21:59:58.611761+00:00
-- url     : https://prove2.me/theorems/ca522ad0-fb23-4a0a-b201-4ace8121db99
-- title:
--   OAI.UniversalTensorSquare.sg4345: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4345` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4345 : RowSquare [8,2,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree41_7All`, `OAI.UniversalTensorSquare.degreeTree43_177All`, `OAI.UniversalTensorSquare.degreeTree43_248All`, `OAI.UniversalTensorSquare.degreeTree43_251All`, `OAI.UniversalTensorSquare.degreeTree43_532All`, `OAI.UniversalTensorSquare.degreeTree43_542All`, `OAI.UniversalTensorSquare.degreeTree43_546All`, `OAI.UniversalTensorSquare.degreeTree43_553All`, `OAI.UniversalTensorSquare.degreeTree43_582All`, `OAI.UniversalTensorSquare.degreeTree43_587All`, `OAI.UniversalTensorSquare.degreeTree43_592All`, `OAI.UniversalTensorSquare.degreeTree43_600All`, `OAI.UniversalTensorSquare.degreeTree43_601All`, `OAI.UniversalTensorSquare.degreeTree43_615All`, `OAI.UniversalTensorSquare.degreeTree43_616All`, `OAI.UniversalTensorSquare.degreeTree43_618All`, `OAI.UniversalTensorSquare.degreeTree43_631All`, `OAI.UniversalTensorSquare.sg14498`, `OAI.UniversalTensorSquare.sg25099`, `OAI.UniversalTensorSquare.sg25121`, `OAI.UniversalTensorSquare.sg25127`, `OAI.UniversalTensorSquare.sg25145`, `OAI.UniversalTensorSquare.sg25174`, `OAI.UniversalTensorSquare.sg25180`, `OAI.UniversalTensorSquare.sg25237`, `OAI.UniversalTensorSquare.sg25291`, `OAI.UniversalTensorSquare.sg25954`, `OAI.UniversalTensorSquare.sg26563`, `OAI.UniversalTensorSquare.sg26796`, `OAI.UniversalTensorSquare.sg26816`, `OAI.UniversalTensorSquare.sg26822`, `OAI.UniversalTensorSquare.sg26858`, `OAI.UniversalTensorSquare.sg29772`, `OAI.UniversalTensorSquare.sg30602`, `OAI.UniversalTensorSquare.sg30609` and `OAI.UniversalTensorSquare.sg31208` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg4345)

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

lemma sg4345 : RowSquare [8,2,1,1,1,1,1,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
