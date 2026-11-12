-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg1169
-- name    : OAI.UniversalTensorSquare.sg1169
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T20:38:03.879835+00:00
-- url     : https://prove2.me/theorems/5e141da6-3d9f-43aa-9bb0-2eb0207eff66
-- title:
--   OAI.UniversalTensorSquare.sg1169: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg1169` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg1169 : RowSquare [3,3,1,1,1,1,1] [6,5]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree24_1All`, `OAI.UniversalTensorSquare.degreeTree26_0All`, `OAI.UniversalTensorSquare.degreeTree43_316All`, `OAI.UniversalTensorSquare.degreeTree43_327All`, `OAI.UniversalTensorSquare.degreeTree43_336All`, `OAI.UniversalTensorSquare.degreeTree43_340All`, `OAI.UniversalTensorSquare.degreeTree43_343All`, `OAI.UniversalTensorSquare.degreeTree43_372All`, `OAI.UniversalTensorSquare.degreeTree43_377All`, `OAI.UniversalTensorSquare.degreeTree43_434All`, `OAI.UniversalTensorSquare.degreeTree43_86All`, `OAI.UniversalTensorSquare.sg19572`, `OAI.UniversalTensorSquare.sg23558`, `OAI.UniversalTensorSquare.sg23560`, `OAI.UniversalTensorSquare.sg24799`, `OAI.UniversalTensorSquare.sg24801`, `OAI.UniversalTensorSquare.sg25093`, `OAI.UniversalTensorSquare.sg25095`, `OAI.UniversalTensorSquare.sg25108`, `OAI.UniversalTensorSquare.sg26566`, `OAI.UniversalTensorSquare.sg26783`, `OAI.UniversalTensorSquare.sg26785`, `OAI.UniversalTensorSquare.sg27049`, `OAI.UniversalTensorSquare.sg27051`, `OAI.UniversalTensorSquare.sg27053`, `OAI.UniversalTensorSquare.sg27078`, `OAI.UniversalTensorSquare.sg27080`, `OAI.UniversalTensorSquare.sg27082`, `OAI.UniversalTensorSquare.sg27162`, `OAI.UniversalTensorSquare.sg27164`, `OAI.UniversalTensorSquare.sg27187`, `OAI.UniversalTensorSquare.sg27189`, `OAI.UniversalTensorSquare.sg27330`, `OAI.UniversalTensorSquare.sg27332`, `OAI.UniversalTensorSquare.sg27854`, `OAI.UniversalTensorSquare.sg27862`, `OAI.UniversalTensorSquare.sg29186`, `OAI.UniversalTensorSquare.sg29998`, `OAI.UniversalTensorSquare.sg31144`, `OAI.UniversalTensorSquare.sg31146`, `OAI.UniversalTensorSquare.sg31148`, `OAI.UniversalTensorSquare.sg31181`, `OAI.UniversalTensorSquare.sg31183`, `OAI.UniversalTensorSquare.sg31253` and `OAI.UniversalTensorSquare.sg31255` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes1.lean (declaration OAI.UniversalTensorSquare.sg1169)

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

lemma sg1169 : RowSquare [3,3,1,1,1,1,1] [6,5] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
