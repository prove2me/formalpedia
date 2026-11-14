-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg11531
-- name    : OAI.UniversalTensorSquare.sg11531
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T20:37:46.878903+00:00
-- url     : https://prove2.me/theorems/04615d41-4637-4c8a-a4ae-f2356eebf215
-- title:
--   OAI.UniversalTensorSquare.sg11531: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg11531` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg11531 : RowSquare [7,6,3,2,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree43_269All`, `OAI.UniversalTensorSquare.degreeTree43_315All`, `OAI.UniversalTensorSquare.degreeTree43_316All`, `OAI.UniversalTensorSquare.degreeTree43_320All`, `OAI.UniversalTensorSquare.degreeTree43_333All`, `OAI.UniversalTensorSquare.degreeTree43_340All`, `OAI.UniversalTensorSquare.degreeTree43_342All`, `OAI.UniversalTensorSquare.degreeTree43_351All`, `OAI.UniversalTensorSquare.degreeTree43_364All`, `OAI.UniversalTensorSquare.degreeTree43_372All`, `OAI.UniversalTensorSquare.degreeTree43_378All`, `OAI.UniversalTensorSquare.degreeTree43_380All`, `OAI.UniversalTensorSquare.degreeTree43_389All`, `OAI.UniversalTensorSquare.degreeTree43_428All`, `OAI.UniversalTensorSquare.degreeTree43_431All`, `OAI.UniversalTensorSquare.degreeTree43_441All`, `OAI.UniversalTensorSquare.degreeTree43_457All`, `OAI.UniversalTensorSquare.degreeTree43_484All`, `OAI.UniversalTensorSquare.degreeTree43_497All`, `OAI.UniversalTensorSquare.degreeTree43_503All`, `OAI.UniversalTensorSquare.degreeTree43_553All`, `OAI.UniversalTensorSquare.degreeTree43_564All`, `OAI.UniversalTensorSquare.sg24750`, `OAI.UniversalTensorSquare.sg25906`, `OAI.UniversalTensorSquare.sg26299`, `OAI.UniversalTensorSquare.sg26961`, `OAI.UniversalTensorSquare.sg26970`, `OAI.UniversalTensorSquare.sg26980`, `OAI.UniversalTensorSquare.sg27020`, `OAI.UniversalTensorSquare.sg27750`, `OAI.UniversalTensorSquare.sg27759`, `OAI.UniversalTensorSquare.sg27807`, `OAI.UniversalTensorSquare.sg27941`, `OAI.UniversalTensorSquare.sg27980`, `OAI.UniversalTensorSquare.sg27998`, `OAI.UniversalTensorSquare.sg28141`, `OAI.UniversalTensorSquare.sg28424`, `OAI.UniversalTensorSquare.sg28442`, `OAI.UniversalTensorSquare.sg28479`, `OAI.UniversalTensorSquare.sg28624`, `OAI.UniversalTensorSquare.sg29149`, `OAI.UniversalTensorSquare.sg29201`, `OAI.UniversalTensorSquare.sg29953`, `OAI.UniversalTensorSquare.sg29962`, `OAI.UniversalTensorSquare.sg29972`, `OAI.UniversalTensorSquare.sg30700`, `OAI.UniversalTensorSquare.sg31112` and `OAI.UniversalTensorSquare.sg31122` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupLocalLeaves.lean (declaration OAI.UniversalTensorSquare.sg11531)

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

lemma sg11531 : RowSquare [7,6,3,2,2,2,1] [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
