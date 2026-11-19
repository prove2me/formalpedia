-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_sg4167
-- name    : OAI.UniversalTensorSquare.sg4167
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T20:24:14.01875+00:00
-- url     : https://prove2.me/theorems/ab69198a-9b0e-44d0-8b68-ffd37753e8cd
-- title:
--   OAI.UniversalTensorSquare.sg4167: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.sg4167` of [lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Columns Saxl.Balance`):
--
--   ```lean
--   lemma sg4167 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,2,2]
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.RowSquare` (definitions bundle `OAIQ259US007` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeTree62_487All`, `OAI.UniversalTensorSquare.degreeTree62_584All`, `OAI.UniversalTensorSquare.degreeTree62_607All`, `OAI.UniversalTensorSquare.degreeTree62_610All`, `OAI.UniversalTensorSquare.degreeTree62_620All`, `OAI.UniversalTensorSquare.degreeTree62_662All`, `OAI.UniversalTensorSquare.degreeTree62_673All`, `OAI.UniversalTensorSquare.degreeTree62_95All`, `OAI.UniversalTensorSquare.degreeTree62_984All`, `OAI.UniversalTensorSquare.sg12619`, `OAI.UniversalTensorSquare.sg12932`, `OAI.UniversalTensorSquare.sg15608`, `OAI.UniversalTensorSquare.sg32081`, `OAI.UniversalTensorSquare.sg32536`, `OAI.UniversalTensorSquare.sg32771`, `OAI.UniversalTensorSquare.sg32823`, `OAI.UniversalTensorSquare.sg32906`, `OAI.UniversalTensorSquare.sg32968`, `OAI.UniversalTensorSquare.sg33016`, `OAI.UniversalTensorSquare.sg33244`, `OAI.UniversalTensorSquare.sg34648`, `OAI.UniversalTensorSquare.sg35545`, `OAI.UniversalTensorSquare.sg35546`, `OAI.UniversalTensorSquare.sg35638`, `OAI.UniversalTensorSquare.sg35708`, `OAI.UniversalTensorSquare.sg35709`, `OAI.UniversalTensorSquare.sg35813`, `OAI.UniversalTensorSquare.sg36229`, `OAI.UniversalTensorSquare.sg36264`, `OAI.UniversalTensorSquare.sg36408`, `OAI.UniversalTensorSquare.sg36840`, `OAI.UniversalTensorSquare.sg37968`, `OAI.UniversalTensorSquare.sg39164`, `OAI.UniversalTensorSquare.sg40649` and `OAI.UniversalTensorSquare.sg42786` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Semigroup/SemigroupNodes9.lean (declaration OAI.UniversalTensorSquare.sg4167)

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

lemma sg4167 : RowSquare [7,3,2,1,1,1,1] [2,2,2,2,2,2,2,2] := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
