-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg55
-- name    : OAI.UniversalTensorSquare.sg55
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-17T22:43:47.347826+00:00
-- url     : https://prove2.me/theorems/7b429e7b-8360-4551-849a-4f0d0bbe5558
-- title:
--   OAI.UniversalTensorSquare.sg55: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg55` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg55 : RowSquare [2,2,1,1] [2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree22_9All`, `OAI.UniversalTensorSquare.degreeTree26_24All`, `OAI.UniversalTensorSquare.degreeTree43_109All`, `OAI.UniversalTensorSquare.degreeTree43_285All`, `OAI.UniversalTensorSquare.degreeTree43_457All`, `OAI.UniversalTensorSquare.degreeTree43_86All`, `OAI.UniversalTensorSquare.sg10983`, `OAI.UniversalTensorSquare.sg18045`, `OAI.UniversalTensorSquare.sg22045`, `OAI.UniversalTensorSquare.sg22515`, `OAI.UniversalTensorSquare.sg22516`, `OAI.UniversalTensorSquare.sg24756`, `OAI.UniversalTensorSquare.sg24759`, `OAI.UniversalTensorSquare.sg26566`, `OAI.UniversalTensorSquare.sg26783`, `OAI.UniversalTensorSquare.sg26785`, `OAI.UniversalTensorSquare.sg27162`, `OAI.UniversalTensorSquare.sg27164`, `OAI.UniversalTensorSquare.sg28869`, `OAI.UniversalTensorSquare.sg31253`, `OAI.UniversalTensorSquare.sg31255`, `OAI.UniversalTensorSquare.sg34250`, `OAI.UniversalTensorSquare.sg34614`, `OAI.UniversalTensorSquare.sg34636`, `OAI.UniversalTensorSquare.sg34677`, `OAI.UniversalTensorSquare.sg34695`, `OAI.UniversalTensorSquare.sg34785`, `OAI.UniversalTensorSquare.sg34799`, `OAI.UniversalTensorSquare.sg34800`, `OAI.UniversalTensorSquare.sg34801`, `OAI.UniversalTensorSquare.sg35710`, `OAI.UniversalTensorSquare.sg36625`, `OAI.UniversalTensorSquare.sg39535`, `OAI.UniversalTensorSquare.sg39557`, `OAI.UniversalTensorSquare.sg39582`, `OAI.UniversalTensorSquare.sg39584`, `OAI.UniversalTensorSquare.sg39601`, `OAI.UniversalTensorSquare.sg39645`, `OAI.UniversalTensorSquare.sg39667`, `OAI.UniversalTensorSquare.sg39669`, `OAI.UniversalTensorSquare.sg39692`, `OAI.UniversalTensorSquare.sg39708`, `OAI.UniversalTensorSquare.sg41943`, `OAI.UniversalTensorSquare.sg42700` and `OAI.UniversalTensorSquare.sg5716` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg55)

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

lemma sg55 : RowSquare [2,2,1,1] [2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
