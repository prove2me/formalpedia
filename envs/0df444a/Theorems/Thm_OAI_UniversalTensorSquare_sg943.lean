-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg943
-- name    : OAI.UniversalTensorSquare.sg943
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-18T00:02:43.300129+00:00
-- url     : https://prove2.me/theorems/dc90a096-2d00-452a-9341-d8c69574e1d1
-- title:
--   OAI.UniversalTensorSquare.sg943: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg943` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg943 : RowSquare [5,2,2,1] [2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_412All`, `OAI.UniversalTensorSquare.sg14557`, `OAI.UniversalTensorSquare.sg14616`, `OAI.UniversalTensorSquare.sg16495`, `OAI.UniversalTensorSquare.sg18035`, `OAI.UniversalTensorSquare.sg18036`, `OAI.UniversalTensorSquare.sg18038`, `OAI.UniversalTensorSquare.sg18043`, `OAI.UniversalTensorSquare.sg18044`, `OAI.UniversalTensorSquare.sg26115`, `OAI.UniversalTensorSquare.sg32185`, `OAI.UniversalTensorSquare.sg32766`, `OAI.UniversalTensorSquare.sg34559`, `OAI.UniversalTensorSquare.sg34560`, `OAI.UniversalTensorSquare.sg34561`, `OAI.UniversalTensorSquare.sg34582`, `OAI.UniversalTensorSquare.sg34583`, `OAI.UniversalTensorSquare.sg34586`, `OAI.UniversalTensorSquare.sg34588`, `OAI.UniversalTensorSquare.sg36031`, `OAI.UniversalTensorSquare.sg36033`, `OAI.UniversalTensorSquare.sg36035`, `OAI.UniversalTensorSquare.sg36279`, `OAI.UniversalTensorSquare.sg36299`, `OAI.UniversalTensorSquare.sg36301`, `OAI.UniversalTensorSquare.sg36306`, `OAI.UniversalTensorSquare.sg37038`, `OAI.UniversalTensorSquare.sg37491`, `OAI.UniversalTensorSquare.sg37673`, `OAI.UniversalTensorSquare.sg37674`, `OAI.UniversalTensorSquare.sg37686`, `OAI.UniversalTensorSquare.sg38898`, `OAI.UniversalTensorSquare.sg38903`, `OAI.UniversalTensorSquare.sg38904`, `OAI.UniversalTensorSquare.sg39969`, `OAI.UniversalTensorSquare.sg39971`, `OAI.UniversalTensorSquare.sg40475`, `OAI.UniversalTensorSquare.sg40477`, `OAI.UniversalTensorSquare.sg40478`, `OAI.UniversalTensorSquare.sg41177`, `OAI.UniversalTensorSquare.sg41840`, `OAI.UniversalTensorSquare.sg42029`, `OAI.UniversalTensorSquare.sg42972`, `OAI.UniversalTensorSquare.sg43019`, `OAI.UniversalTensorSquare.sg6641`, `OAI.UniversalTensorSquare.sg6642`, `OAI.UniversalTensorSquare.sg6651` and `OAI.UniversalTensorSquare.sg6677` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLeaves5.lean (declaration OAI.UniversalTensorSquare.sg943)

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

lemma sg943 : RowSquare [5,2,2,1] [2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
